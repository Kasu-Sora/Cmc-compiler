#include "proof/proof.h"
#include "userlib/renderers.h"
#include "tower_base.h"
#require "tower_base.c"
#include "cmc_lang.h"
#include "userlib/proof.h"

PROOF static size_t _cmc_lang_axioms_before = vector_size(get_all_axioms());

/* Source types and tagged values. */
PROOF indtype cm_type_ty = new_datatype_definition(
    "cm_type = CMIntTy | CMCharTy | CMStructTy int | CMPtrTy cm_type");
PROOF thm cm_type_RECURSION = cm_type_ty.rec;
PROOF static int _t_cm_type = cst_add_type_to_header("cm_type", 0);
PROOF static int _c_CMIntTy = cst_add_const_to_header(`CMIntTy:cm_type`);
PROOF static int _c_CMCharTy = cst_add_const_to_header(`CMCharTy:cm_type`);
PROOF static int _c_CMStructTy =
    cst_add_const_to_header(`CMStructTy:int->cm_type`);
PROOF static int _c_CMPtrTy =
    cst_add_const_to_header(`CMPtrTy:cm_type->cm_type`);

PROOF indtype cm_value_ty = new_datatype_definition(
    "cm_value = CMIntV int | CMCharV int | CMNullV"
    " | CMPtrV int int int int cm_type");
PROOF thm cm_value_RECURSION = cm_value_ty.rec;
PROOF static int _t_cm_value = cst_add_type_to_header("cm_value", 0);
PROOF static int _c_CMIntV = cst_add_const_to_header(`CMIntV:int->cm_value`);
PROOF static int _c_CMCharV = cst_add_const_to_header(`CMCharV:int->cm_value`);
PROOF static int _c_CMNullV = cst_add_const_to_header(`CMNullV:cm_value`);
PROOF static int _c_CMPtrV = cst_add_const_to_header(
    `CMPtrV:int->int->int->int->cm_type->cm_value`);

/* Typed, resolved syntax. */
PROOF indtype cm_expr_ty = new_datatype_definition(
    "cm_expr = CMConstE int cm_type | CMStringE int cm_type"
    " | CMVarE int int cm_type | CMAssignE cm_expr cm_expr cm_type"
    " | CMBinaryE int cm_expr cm_expr cm_type"
    " | CMUnaryE int cm_expr cm_type | CMIndexE cm_expr cm_expr cm_type"
    " | CMMemberE cm_expr int cm_type"
    " | CMCallE int (cm_expr)list cm_type"
    " | CMSizeofE cm_type cm_type | CMGetcE cm_type"
    " | CMPutcE cm_expr cm_type | CMPutiE cm_expr cm_type"
    " | CMExitE cm_expr cm_type");
PROOF thm cm_expr_RECURSION = cm_expr_ty.rec;
PROOF static int _t_cm_expr = cst_add_type_to_header("cm_expr", 0);
PROOF static int _c_CMConstE =
    cst_add_const_to_header(`CMConstE:int->cm_type->cm_expr`);
PROOF static int _c_CMStringE =
    cst_add_const_to_header(`CMStringE:int->cm_type->cm_expr`);
PROOF static int _c_CMVarE =
    cst_add_const_to_header(`CMVarE:int->int->cm_type->cm_expr`);
PROOF static int _c_CMAssignE = cst_add_const_to_header(
    `CMAssignE:cm_expr->cm_expr->cm_type->cm_expr`);
PROOF static int _c_CMBinaryE = cst_add_const_to_header(
    `CMBinaryE:int->cm_expr->cm_expr->cm_type->cm_expr`);
PROOF static int _c_CMUnaryE = cst_add_const_to_header(
    `CMUnaryE:int->cm_expr->cm_type->cm_expr`);
PROOF static int _c_CMIndexE = cst_add_const_to_header(
    `CMIndexE:cm_expr->cm_expr->cm_type->cm_expr`);
PROOF static int _c_CMMemberE = cst_add_const_to_header(
    `CMMemberE:cm_expr->int->cm_type->cm_expr`);
PROOF static int _c_CMCallE = cst_add_const_to_header(
    `CMCallE:int->(cm_expr)list->cm_type->cm_expr`);
PROOF static int _c_CMSizeofE = cst_add_const_to_header(
    `CMSizeofE:cm_type->cm_type->cm_expr`);
PROOF static int _c_CMGetcE =
    cst_add_const_to_header(`CMGetcE:cm_type->cm_expr`);
PROOF static int _c_CMPutcE = cst_add_const_to_header(
    `CMPutcE:cm_expr->cm_type->cm_expr`);
PROOF static int _c_CMPutiE = cst_add_const_to_header(
    `CMPutiE:cm_expr->cm_type->cm_expr`);
PROOF static int _c_CMExitE = cst_add_const_to_header(
    `CMExitE:cm_expr->cm_type->cm_expr`);

PROOF indtype cm_stmt_ty = new_datatype_definition(
    "cm_stmt = CMSkipS | CMExprS cm_expr | CMDeclS int"
    " | CMInitS int cm_expr | CMSeqS cm_stmt cm_stmt | CMBlockS cm_stmt"
    " | CMIfS cm_expr cm_stmt cm_stmt | CMWhileS cm_expr cm_stmt"
    " | CMBreakS | CMContinueS | CMReturnS cm_expr");
PROOF thm cm_stmt_RECURSION = cm_stmt_ty.rec;
PROOF static int _t_cm_stmt = cst_add_type_to_header("cm_stmt", 0);
PROOF static int _c_CMSkipS = cst_add_const_to_header(`CMSkipS:cm_stmt`);
PROOF static int _c_CMExprS =
    cst_add_const_to_header(`CMExprS:cm_expr->cm_stmt`);
PROOF static int _c_CMDeclS = cst_add_const_to_header(`CMDeclS:int->cm_stmt`);
PROOF static int _c_CMInitS =
    cst_add_const_to_header(`CMInitS:int->cm_expr->cm_stmt`);
PROOF static int _c_CMSeqS =
    cst_add_const_to_header(`CMSeqS:cm_stmt->cm_stmt->cm_stmt`);
PROOF static int _c_CMBlockS =
    cst_add_const_to_header(`CMBlockS:cm_stmt->cm_stmt`);
PROOF static int _c_CMIfS = cst_add_const_to_header(
    `CMIfS:cm_expr->cm_stmt->cm_stmt->cm_stmt`);
PROOF static int _c_CMWhileS = cst_add_const_to_header(
    `CMWhileS:cm_expr->cm_stmt->cm_stmt`);
PROOF static int _c_CMBreakS = cst_add_const_to_header(`CMBreakS:cm_stmt`);
PROOF static int _c_CMContinueS =
    cst_add_const_to_header(`CMContinueS:cm_stmt`);
PROOF static int _c_CMReturnS =
    cst_add_const_to_header(`CMReturnS:cm_expr->cm_stmt`);

/* Descriptor lists use dense list position as their resolved identifier. */
PROOF indtype cm_slot_d_ty = new_datatype_definition(
    "cm_slot_d = CMSlotD cm_type int");
PROOF static int _t_cm_slot_d = cst_add_type_to_header("cm_slot_d", 0);
PROOF static int _c_CMSlotD =
    cst_add_const_to_header(`CMSlotD:cm_type->int->cm_slot_d`);

PROOF indtype cm_struct_d_ty = new_datatype_definition(
    "cm_struct_d = CMStructD (cm_slot_d)list");
PROOF static int _t_cm_struct_d = cst_add_type_to_header("cm_struct_d", 0);
PROOF static int _c_CMStructD =
    cst_add_const_to_header(`CMStructD:(cm_slot_d)list->cm_struct_d`);

PROOF indtype cm_global_d_ty = new_datatype_definition(
    "cm_global_d = CMGlobalD cm_type int bool int");
PROOF static int _t_cm_global_d = cst_add_type_to_header("cm_global_d", 0);
PROOF static int _c_CMGlobalD = cst_add_const_to_header(
    `CMGlobalD:cm_type->int->bool->int->cm_global_d`);

PROOF indtype cm_string_d_ty = new_datatype_definition(
    "cm_string_d = CMStringD (int)list");
PROOF static int _t_cm_string_d = cst_add_type_to_header("cm_string_d", 0);
PROOF static int _c_CMStringD =
    cst_add_const_to_header(`CMStringD:(int)list->cm_string_d`);

PROOF indtype cm_function_d_ty = new_datatype_definition(
    "cm_function_d = CMFunctionD cm_type (cm_slot_d)list"
    " (cm_slot_d)list cm_stmt");
PROOF static int _t_cm_function_d =
    cst_add_type_to_header("cm_function_d", 0);
PROOF static int _c_CMFunctionD = cst_add_const_to_header(
    `CMFunctionD:cm_type->(cm_slot_d)list->(cm_slot_d)list->cm_stmt->cm_function_d`);

PROOF indtype cm_program_ty = new_datatype_definition(
    "cm_program = CMProgram (cm_struct_d)list (cm_global_d)list"
    " (cm_string_d)list (cm_function_d)list int");
PROOF thm cm_program_RECURSION = cm_program_ty.rec;
PROOF static int _t_cm_program = cst_add_type_to_header("cm_program", 0);
PROOF static int _c_CMProgram = cst_add_const_to_header(
    `CMProgram:(cm_struct_d)list->(cm_global_d)list->(cm_string_d)list->(cm_function_d)list->int->cm_program`);

PROOF thm get_cm_type_recursion(void) { return cm_type_RECURSION; }
PROOF thm get_cm_value_recursion(void) { return cm_value_RECURSION; }
PROOF thm get_cm_expr_recursion(void) { return cm_expr_RECURSION; }
PROOF thm get_cm_stmt_recursion(void) { return cm_stmt_RECURSION; }
PROOF thm get_cm_program_recursion(void) { return cm_program_RECURSION; }
PROOF thm get_cm_expr_induction(void) { return cm_expr_ty.ind; }
PROOF thm get_cm_expr_cases(void) {
  return conjunct1_rule(get_datatype_cases("cm_expr"));
}
PROOF thm get_cm_stmt_induction(void) { return cm_stmt_ty.ind; }
PROOF thm get_cm_stmt_cases(void) {
  return get_datatype_cases("cm_stmt");
}

/* --------------------------------------------------------------------- */
/* Total descriptor selectors.  Well-formedness supplies range facts.    */
/* --------------------------------------------------------------------- */

PROOF thm cm_slot_ty_def = new_rec_definition(cm_slot_d_ty.rec,
    `cm_slot_ty (CMSlotD (ty:cm_type) (count:int)) = ty`);
PROOF thm cm_slot_count_def = new_rec_definition(cm_slot_d_ty.rec,
    `cm_slot_count (CMSlotD (ty:cm_type) (count:int)) = count`);
PROOF int _e_cm_slot_ty = cst_add_const_to_header(`cm_slot_ty`);
PROOF int _e_cm_slot_count = cst_add_const_to_header(`cm_slot_count`);

PROOF thm cm_struct_members_def = new_rec_definition(cm_struct_d_ty.rec,
    `cm_struct_members (CMStructD (members:(cm_slot_d)list)) = members`);
PROOF int _e_cm_struct_members = cst_add_const_to_header(`cm_struct_members`);

PROOF thm cm_global_ty_def = new_rec_definition(cm_global_d_ty.rec,
    `cm_global_ty (CMGlobalD (ty:cm_type) (count:int) (has_init:bool) (init:int)) = ty`);
PROOF thm cm_global_count_def = new_rec_definition(cm_global_d_ty.rec,
    `cm_global_count (CMGlobalD (ty:cm_type) (count:int) (has_init:bool) (init:int)) = count`);
PROOF thm cm_global_has_init_def = new_rec_definition(cm_global_d_ty.rec,
    `cm_global_has_init (CMGlobalD (ty:cm_type) (count:int) (has_init:bool) (init:int)) = has_init`);
PROOF thm cm_global_init_def = new_rec_definition(cm_global_d_ty.rec,
    `cm_global_init (CMGlobalD (ty:cm_type) (count:int) (has_init:bool) (init:int)) = init`);
PROOF int _e_cm_global_ty = cst_add_const_to_header(`cm_global_ty`);
PROOF int _e_cm_global_count = cst_add_const_to_header(`cm_global_count`);
PROOF int _e_cm_global_has_init = cst_add_const_to_header(`cm_global_has_init`);
PROOF int _e_cm_global_init = cst_add_const_to_header(`cm_global_init`);

PROOF thm cm_string_bytes_def = new_rec_definition(cm_string_d_ty.rec,
    `cm_string_bytes (CMStringD (bytes:(int)list)) = bytes`);
PROOF int _e_cm_string_bytes = cst_add_const_to_header(`cm_string_bytes`);

PROOF thm cm_function_ret_def = new_rec_definition(cm_function_d_ty.rec,
    `cm_function_ret
       (CMFunctionD (ret:cm_type) (params:(cm_slot_d)list)
          (locals:(cm_slot_d)list) (body:cm_stmt)) = ret`);
PROOF thm cm_function_params_def = new_rec_definition(cm_function_d_ty.rec,
    `cm_function_params
       (CMFunctionD (ret:cm_type) (params:(cm_slot_d)list)
          (locals:(cm_slot_d)list) (body:cm_stmt)) = params`);
PROOF thm cm_function_locals_def = new_rec_definition(cm_function_d_ty.rec,
    `cm_function_locals
       (CMFunctionD (ret:cm_type) (params:(cm_slot_d)list)
          (locals:(cm_slot_d)list) (body:cm_stmt)) = locals`);
PROOF thm cm_function_body_def = new_rec_definition(cm_function_d_ty.rec,
    `cm_function_body
       (CMFunctionD (ret:cm_type) (params:(cm_slot_d)list)
          (locals:(cm_slot_d)list) (body:cm_stmt)) = body`);
PROOF int _e_cm_function_ret = cst_add_const_to_header(`cm_function_ret`);
PROOF int _e_cm_function_params = cst_add_const_to_header(`cm_function_params`);
PROOF int _e_cm_function_locals = cst_add_const_to_header(`cm_function_locals`);
PROOF int _e_cm_function_body = cst_add_const_to_header(`cm_function_body`);

PROOF thm cm_program_structs_def = new_rec_definition(cm_program_ty.rec,
    `cm_program_structs
       (CMProgram (structs:(cm_struct_d)list) (globals:(cm_global_d)list)
          (strings:(cm_string_d)list) (functions:(cm_function_d)list)
          (main_id:int)) = structs`);
PROOF thm cm_program_globals_def = new_rec_definition(cm_program_ty.rec,
    `cm_program_globals
       (CMProgram (structs:(cm_struct_d)list) (globals:(cm_global_d)list)
          (strings:(cm_string_d)list) (functions:(cm_function_d)list)
          (main_id:int)) = globals`);
PROOF thm cm_program_strings_def = new_rec_definition(cm_program_ty.rec,
    `cm_program_strings
       (CMProgram (structs:(cm_struct_d)list) (globals:(cm_global_d)list)
          (strings:(cm_string_d)list) (functions:(cm_function_d)list)
          (main_id:int)) = strings`);
PROOF thm cm_program_functions_def = new_rec_definition(cm_program_ty.rec,
    `cm_program_functions
       (CMProgram (structs:(cm_struct_d)list) (globals:(cm_global_d)list)
          (strings:(cm_string_d)list) (functions:(cm_function_d)list)
          (main_id:int)) = functions`);
PROOF thm cm_program_main_def = new_rec_definition(cm_program_ty.rec,
    `cm_program_main
       (CMProgram (structs:(cm_struct_d)list) (globals:(cm_global_d)list)
          (strings:(cm_string_d)list) (functions:(cm_function_d)list)
          (main_id:int)) = main_id`);
PROOF int _e_cm_program_structs = cst_add_const_to_header(`cm_program_structs`);
PROOF int _e_cm_program_globals = cst_add_const_to_header(`cm_program_globals`);
PROOF int _e_cm_program_strings = cst_add_const_to_header(`cm_program_strings`);
PROOF int _e_cm_program_functions = cst_add_const_to_header(`cm_program_functions`);
PROOF int _e_cm_program_main = cst_add_const_to_header(`cm_program_main`);

/* --------------------------------------------------------------------- */
/* Exact padless layouts.  Direct struct-valued members are rejected by  */
/* cm_typed_program; this makes the acyclic leaf-size fold total.         */
/* --------------------------------------------------------------------- */

PROOF thm cm_leaf_size_def = new_rec_definition(cm_type_RECURSION,
    `(cm_leaf_size CMIntTy = 8i) &&
     (cm_leaf_size CMCharTy = 1i) &&
     (!sid. cm_leaf_size (CMStructTy (sid:int)) = 0i) &&
     (!ty. cm_leaf_size (CMPtrTy (ty:cm_type)) = 8i)`);
PROOF int _e_cm_leaf_size = cst_add_const_to_header(`cm_leaf_size`);

PROOF thm cm_struct_member_size_def = new_fun_definition(
    `cm_struct_member_size (slot:cm_slot_d) : int =
       (if cm_slot_count slot == 0i
        then cm_leaf_size (cm_slot_ty slot)
        else cm_slot_count slot * cm_leaf_size (cm_slot_ty slot))`);
PROOF int _e_cm_struct_member_size =
    cst_add_const_to_header(`cm_struct_member_size`);

PROOF thm cm_struct_slots_size_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_struct_slots_size ([]:(cm_slot_d)list) = 0i) &&
     (!slot rest.
        cm_struct_slots_size
          ((slot:cm_slot_d) :: (rest:(cm_slot_d)list)) =
        cm_struct_member_size slot + cm_struct_slots_size rest)`);
PROOF int _e_cm_struct_slots_size =
    cst_add_const_to_header(`cm_struct_slots_size`);

PROOF thm cm_struct_size_def = new_fun_definition(
    `cm_struct_size (structs:(cm_struct_d)list) (sid:int) : int =
       (if 0i <= sid && sid < ilength structs
        then cm_struct_slots_size (cm_struct_members (inth sid structs))
        else 0i)`);
PROOF int _e_cm_struct_size = cst_add_const_to_header(`cm_struct_size`);

PROOF thm cm_type_size_def = new_rec_definition(cm_type_RECURSION,
    `(cm_type_size (structs:(cm_struct_d)list) CMIntTy = 8i) &&
     (cm_type_size (structs:(cm_struct_d)list) CMCharTy = 1i) &&
     (!sid. cm_type_size structs (CMStructTy (sid:int)) =
        cm_struct_size structs sid) &&
     (!ty. cm_type_size structs (CMPtrTy (ty:cm_type)) = 8i)`);
PROOF int _e_cm_type_size = cst_add_const_to_header(`cm_type_size`);

PROOF thm cm_slot_size_def = new_fun_definition(
    `cm_slot_size (structs:(cm_struct_d)list) (slot:cm_slot_d) : int =
       (if cm_slot_count slot == 0i
        then cm_type_size structs (cm_slot_ty slot)
        else cm_slot_count slot * cm_type_size structs (cm_slot_ty slot))`);
PROOF int _e_cm_slot_size = cst_add_const_to_header(`cm_slot_size`);

PROOF thm cm_slots_size_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_slots_size (structs:(cm_struct_d)list) ([]:(cm_slot_d)list) = 0i) &&
     (!slot rest.
        cm_slots_size structs
          ((slot:cm_slot_d) :: (rest:(cm_slot_d)list)) =
        cm_slot_size structs slot + cm_slots_size structs rest)`);
PROOF int _e_cm_slots_size = cst_add_const_to_header(`cm_slots_size`);

PROOF thm cm_member_offset_slots_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_member_offset_slots ([]:(cm_slot_d)list) (mid:int) = 0i) &&
     (!slot rest mid.
        cm_member_offset_slots
          ((slot:cm_slot_d) :: (rest:(cm_slot_d)list)) (mid:int) =
        (if mid == 0i then 0i
         else cm_struct_member_size slot +
              cm_member_offset_slots rest (mid - 1i)))`);
PROOF int _e_cm_member_offset_slots =
    cst_add_const_to_header(`cm_member_offset_slots`);

PROOF thm cm_member_offset_def = new_fun_definition(
    `cm_member_offset (structs:(cm_struct_d)list) (sid:int) (mid:int) : int =
       (if 0i <= sid && sid < ilength structs
        then cm_member_offset_slots
               (cm_struct_members (inth sid structs)) mid
        else 0i)`);
PROOF int _e_cm_member_offset = cst_add_const_to_header(`cm_member_offset`);

PROOF thm cm_global_size_def = new_fun_definition(
    `cm_global_size (structs:(cm_struct_d)list) (g:cm_global_d) : int =
       (if cm_global_count g == 0i
        then cm_type_size structs (cm_global_ty g)
        else cm_global_count g * cm_type_size structs (cm_global_ty g))`);
PROOF int _e_cm_global_size = cst_add_const_to_header(`cm_global_size`);

PROOF thm cm_globals_size_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_globals_size (structs:(cm_struct_d)list)
        ([]:(cm_global_d)list) = 0i) &&
     (!g rest.
        cm_globals_size structs
          ((g:cm_global_d) :: (rest:(cm_global_d)list)) =
        cm_global_size structs g + cm_globals_size structs rest)`);
PROOF int _e_cm_globals_size = cst_add_const_to_header(`cm_globals_size`);

PROOF thm cm_strings_size_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_strings_size ([]:(cm_string_d)list) = 0i) &&
     (!s rest.
        cm_strings_size
          ((s:cm_string_d) :: (rest:(cm_string_d)list)) =
        ilength (cm_string_bytes s) + 1i + cm_strings_size rest)`);
PROOF int _e_cm_strings_size = cst_add_const_to_header(`cm_strings_size`);

PROOF thm cm_static_size_def = new_fun_definition(
    `cm_static_size (p:cm_program) : int =
       16i +
       cm_globals_size (cm_program_structs p) (cm_program_globals p) +
       cm_strings_size (cm_program_strings p)`);
PROOF int _e_cm_static_size = cst_add_const_to_header(`cm_static_size`);

PROOF thm get_cm_leaf_size_def(void) { return cm_leaf_size_def; }
PROOF thm get_cm_struct_member_size_def(void) {
  return cm_struct_member_size_def;
}
PROOF thm get_cm_struct_slots_size_def(void) {
  return cm_struct_slots_size_def;
}
PROOF thm get_cm_slots_size_def(void) { return cm_slots_size_def; }
PROOF thm get_cm_member_offset_slots_def(void) {
  return cm_member_offset_slots_def;
}
PROOF thm get_cm_type_size_def(void) { return cm_type_size_def; }
PROOF thm get_cm_slot_size_def(void) { return cm_slot_size_def; }
PROOF thm get_cm_member_offset_def(void) { return cm_member_offset_def; }
PROOF thm get_cm_struct_size_def(void) { return cm_struct_size_def; }
PROOF thm get_cm_static_size_def(void) { return cm_static_size_def; }

/* --------------------------------------------------------------------- */
/* Exact temporary-slot recurrences.  The nested expression-list fold is */
/* generated by the datatype package, so call arguments stay structural. */
/* --------------------------------------------------------------------- */

PROOF indtype cm_tpair_ty =
    new_datatype_definition("cm_tpair = CMTPair int int");
PROOF static int _t_cm_tpair = cst_add_type_to_header("cm_tpair", 0);
PROOF static int _c_CMTPair =
    cst_add_const_to_header(`CMTPair:int->int->cm_tpair`);

PROOF indtype cm_apair_ty =
    new_datatype_definition("cm_apair = CMAPair int int");
PROOF static int _t_cm_apair = cst_add_type_to_header("cm_apair", 0);
PROOF static int _c_CMAPair =
    cst_add_const_to_header(`CMAPair:int->int->cm_apair`);

PROOF thm cm_tleft_def = new_rec_definition(cm_tpair_ty.rec,
    `cm_tleft (CMTPair (left:int) (right:int)) = left`);
PROOF thm cm_tright_def = new_rec_definition(cm_tpair_ty.rec,
    `cm_tright (CMTPair (left:int) (right:int)) = right`);
PROOF thm cm_acount_def = new_rec_definition(cm_apair_ty.rec,
    `cm_acount (CMAPair (count:int) (depth:int)) = count`);
PROOF thm cm_adepth_def = new_rec_definition(cm_apair_ty.rec,
    `cm_adepth (CMAPair (count:int) (depth:int)) = depth`);
PROOF int _e_cm_tleft = cst_add_const_to_header(`cm_tleft`);
PROOF int _e_cm_tright = cst_add_const_to_header(`cm_tright`);
PROOF int _e_cm_acount = cst_add_const_to_header(`cm_acount`);
PROOF int _e_cm_adepth = cst_add_const_to_header(`cm_adepth`);

PROOF thm cm_imax_def = new_fun_definition(
    `cm_imax (x:int) (y:int) : int = (if x <= y then y else x)`);
PROOF int _e_cm_imax = cst_add_const_to_header(`cm_imax`);

PROOF thm cm_expr_tpair_def = new_rec_definition(cm_expr_RECURSION,
    `(cm_expr_tpair (CMConstE (n:int) (ty:cm_type)) = CMTPair 0i 0i) &&
     (cm_expr_tpair (CMStringE (sid:int) (ty:cm_type)) = CMTPair 0i 0i) &&
     (cm_expr_tpair (CMVarE (scope:int) (slot:int) (ty:cm_type)) =
        CMTPair 0i 0i) &&
     (!dst src ty.
        cm_expr_tpair
          (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) =
        CMTPair 0i
          (cm_imax (cm_tleft (cm_expr_tpair dst))
                   (1i + cm_tright (cm_expr_tpair src)))) &&
     (!op left right ty.
        cm_expr_tpair
          (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
             (ty:cm_type)) =
        CMTPair 0i
          (if op == 0i || op == 1i
           then cm_imax (cm_tright (cm_expr_tpair left))
                        (cm_tright (cm_expr_tpair right))
           else cm_imax (cm_tright (cm_expr_tpair left))
                        (1i + cm_tright (cm_expr_tpair right)))) &&
     (!op arg ty.
        cm_expr_tpair
          (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) =
        (if op == 2i
         then CMTPair (cm_tright (cm_expr_tpair arg))
                      (cm_tright (cm_expr_tpair arg))
         else if op == 3i
              then CMTPair 0i (cm_tleft (cm_expr_tpair arg))
              else CMTPair 0i (cm_tright (cm_expr_tpair arg)))) &&
     (!base index ty.
        cm_expr_tpair
          (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) =
        CMTPair
          (cm_imax (cm_tright (cm_expr_tpair base))
                   (1i + cm_tright (cm_expr_tpair index)))
          (cm_imax (cm_tright (cm_expr_tpair base))
                   (1i + cm_tright (cm_expr_tpair index)))) &&
     (!base mid ty.
        cm_expr_tpair
          (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) =
        CMTPair (cm_tright (cm_expr_tpair base))
                (cm_tright (cm_expr_tpair base))) &&
     (!fid args ty.
        cm_expr_tpair
          (CMCallE (fid:int) (args:(cm_expr)list) (ty:cm_type)) =
        CMTPair 0i
          (cm_acount (cm_args_apair args) +
           cm_adepth (cm_args_apair args))) &&
     (!asked ty.
        cm_expr_tpair
          (CMSizeofE (asked:cm_type) (ty:cm_type)) = CMTPair 0i 0i) &&
     (!ty. cm_expr_tpair (CMGetcE (ty:cm_type)) = CMTPair 0i 0i) &&
     (!arg ty.
        cm_expr_tpair (CMPutcE (arg:cm_expr) (ty:cm_type)) =
        CMTPair 0i (cm_tright (cm_expr_tpair arg))) &&
     (!arg ty.
        cm_expr_tpair (CMPutiE (arg:cm_expr) (ty:cm_type)) =
        CMTPair 0i (cm_tright (cm_expr_tpair arg))) &&
     (!arg ty.
        cm_expr_tpair (CMExitE (arg:cm_expr) (ty:cm_type)) =
        CMTPair 0i (cm_tright (cm_expr_tpair arg))) &&
     (cm_args_apair ([]:(cm_expr)list) = CMAPair 0i 0i) &&
     (!arg args.
        cm_args_apair
          ((arg:cm_expr) :: (args:(cm_expr)list)) =
        CMAPair (1i + cm_acount (cm_args_apair args))
          (cm_imax (cm_tright (cm_expr_tpair arg))
                   (cm_adepth (cm_args_apair args))))`);
PROOF int _e_cm_expr_tpair = cst_add_const_to_header(`cm_expr_tpair`);
PROOF int _e_cm_args_apair = cst_add_const_to_header(`cm_args_apair`);

PROOF thm cm_ltemps_def = new_fun_definition(
    `cm_ltemps (expr:cm_expr) : int =
       cm_tleft (cm_expr_tpair expr)`);
PROOF thm cm_rtemps_def = new_fun_definition(
    `cm_rtemps (expr:cm_expr) : int =
       cm_tright (cm_expr_tpair expr)`);
PROOF thm cm_args_temps_def = new_fun_definition(
    `cm_args_temps (args:(cm_expr)list) : int =
       cm_acount (cm_args_apair args) +
       cm_adepth (cm_args_apair args)`);
PROOF int _e_cm_ltemps = cst_add_const_to_header(`cm_ltemps`);
PROOF int _e_cm_rtemps = cst_add_const_to_header(`cm_rtemps`);
PROOF int _e_cm_args_temps = cst_add_const_to_header(`cm_args_temps`);

PROOF thm cm_stemps_def = new_rec_definition(cm_stmt_RECURSION,
    `(cm_stemps CMSkipS = 0i) &&
     (!expr. cm_stemps (CMExprS (expr:cm_expr)) = cm_rtemps expr) &&
     (!slot. cm_stemps (CMDeclS (slot:int)) = 0i) &&
     (!slot expr.
        cm_stemps (CMInitS (slot:int) (expr:cm_expr)) =
        cm_rtemps expr) &&
     (!first second.
        cm_stemps (CMSeqS (first:cm_stmt) (second:cm_stmt)) =
        cm_imax (cm_stemps first) (cm_stemps second)) &&
     (!body. cm_stemps (CMBlockS (body:cm_stmt)) = cm_stemps body) &&
     (!guard yes no.
        cm_stemps
          (CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)) =
        cm_imax (cm_rtemps guard)
          (cm_imax (cm_stemps yes) (cm_stemps no))) &&
     (!guard body.
        cm_stemps (CMWhileS (guard:cm_expr) (body:cm_stmt)) =
        cm_imax (cm_rtemps guard) (cm_stemps body)) &&
     (cm_stemps CMBreakS = 0i) &&
     (cm_stemps CMContinueS = 0i) &&
     (!expr. cm_stemps (CMReturnS (expr:cm_expr)) = cm_rtemps expr)`);
PROOF int _e_cm_stemps = cst_add_const_to_header(`cm_stemps`);

PROOF thm cm_temp_slots_def = new_fun_definition(
    `cm_temp_slots (f:cm_function_d) : int =
       cm_stemps (cm_function_body f)`);
PROOF int _e_cm_temp_slots = cst_add_const_to_header(`cm_temp_slots`);

PROOF thm cm_frame_size_def = new_fun_definition(
    `cm_frame_size (structs:(cm_struct_d)list) (f:cm_function_d) : int =
       8i +
       cm_slots_size structs (cm_function_params f) +
       cm_slots_size structs (cm_function_locals f) +
       8i * cm_temp_slots f`);
PROOF int _e_cm_frame_size = cst_add_const_to_header(`cm_frame_size`);

PROOF thm get_cm_frame_size_def(void) { return cm_frame_size_def; }
PROOF thm get_cm_ltemps_def(void) { return cm_ltemps_def; }
PROOF thm get_cm_rtemps_def(void) { return cm_rtemps_def; }
PROOF thm get_cm_args_temps_def(void) { return cm_args_temps_def; }
PROOF thm get_cm_stemps_def(void) { return cm_stemps_def; }
PROOF thm get_cm_temp_slots_def(void) { return cm_temp_slots_def; }
PROOF thm get_cm_imax_def(void) { return cm_imax_def; }
PROOF thm get_cm_tleft_def(void) { return cm_tleft_def; }
PROOF thm get_cm_tright_def(void) { return cm_tright_def; }
PROOF thm get_cm_acount_def(void) { return cm_acount_def; }
PROOF thm get_cm_adepth_def(void) { return cm_adepth_def; }
PROOF thm get_cm_expr_tpair_def(void) { return cm_expr_tpair_def; }
/* --------------------------------------------------------------------- */
/* Stable type codes: the low radix-1024 digit identifies the base type; */
/* each pointer layer adds one to the radix-1024 high-part depth.         */
/* --------------------------------------------------------------------- */

PROOF thm cm_type_depth_def = new_rec_definition(cm_type_RECURSION,
    `(cm_type_depth CMIntTy = 0i) &&
     (cm_type_depth CMCharTy = 0i) &&
     (!sid. cm_type_depth (CMStructTy (sid:int)) = 0i) &&
     (!ty. cm_type_depth (CMPtrTy (ty:cm_type)) =
        1i + cm_type_depth ty)`);
PROOF int _e_cm_type_depth = cst_add_const_to_header(`cm_type_depth`);

PROOF thm cm_type_strip_def = new_rec_definition(cm_type_RECURSION,
    `(cm_type_strip CMIntTy = CMIntTy) &&
     (cm_type_strip CMCharTy = CMCharTy) &&
     (!sid. cm_type_strip (CMStructTy (sid:int)) = CMStructTy sid) &&
     (!ty. cm_type_strip (CMPtrTy (ty:cm_type)) =
        cm_type_strip ty)`);
PROOF int _e_cm_type_strip = cst_add_const_to_header(`cm_type_strip`);

PROOF thm cm_type_base_code_def = new_rec_definition(cm_type_RECURSION,
    `(cm_type_base_code CMIntTy = 0i) &&
     (cm_type_base_code CMCharTy = 1i) &&
     (!sid. cm_type_base_code (CMStructTy (sid:int)) = sid + 2i) &&
     (!ty. cm_type_base_code (CMPtrTy (ty:cm_type)) =
        cm_type_base_code ty)`);
PROOF int _e_cm_type_base_code =
    cst_add_const_to_header(`cm_type_base_code`);

PROOF thm cm_type_code_wf_def = new_rec_definition(cm_type_RECURSION,
    `(cm_type_code_wf CMIntTy = T) &&
     (cm_type_code_wf CMCharTy = T) &&
     (!sid. cm_type_code_wf (CMStructTy (sid:int)) <=>
        0i <= sid && sid < 1022i) &&
     (!ty. cm_type_code_wf (CMPtrTy (ty:cm_type)) <=>
        cm_type_code_wf ty)`);
PROOF int _e_cm_type_code_wf =
    cst_add_const_to_header(`cm_type_code_wf`);

PROOF thm cm_type_base_decode_def = new_fun_definition(
    `cm_type_base_decode (code:int) : cm_type =
       (if code == 0i then CMIntTy
        else if code == 1i then CMCharTy
        else CMStructTy (code - 2i))`);
PROOF int _e_cm_type_base_decode =
    cst_add_const_to_header(`cm_type_base_decode`);

PROOF thm cm_add_ptrs_def = new_rec_definition(
    get_theorem_by_name("num_RECURSION"),
    `(cm_add_ptrs 0 (base:cm_type) = base) &&
     (!n base.
        cm_add_ptrs (SUC (n:num)) (base:cm_type) =
        CMPtrTy (cm_add_ptrs n base))`);
PROOF int _e_cm_add_ptrs = cst_add_const_to_header(`cm_add_ptrs`);

PROOF thm cm_type_encode_def = new_fun_definition(
    `cm_type_encode (ty:cm_type) : int =
       1024i * cm_type_depth ty + cm_type_base_code ty`);
PROOF int _e_cm_type_encode = cst_add_const_to_header(`cm_type_encode`);

PROOF thm cm_type_decode_def = new_fun_definition(
    `cm_type_decode (code:int) : cm_type =
       cm_add_ptrs (num_of_int (code / 1024i))
         (cm_type_base_decode (code % 1024i))`);
PROOF int _e_cm_type_decode = cst_add_const_to_header(`cm_type_decode`);


PROOF thm mk_cm_type_depth_nonneg(void) {
  gnode root =
      gnode_new_with_ccl(`!(ty:cm_type). 0i <= cm_type_depth ty`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < 3; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(cm_type_depth_def)));
  }
  gnode ptr = AUTO_INTROS_TAC(cases[3]);
  thm ih = assume_rule(goal_lasmps(ptr->g)[0].tm);
  thm rhs = mp_rule(inst_rule(TERM_PAIR_LIST(
      (term_pair){`cm_type_depth (a:cm_type)`, `d:int`}),
      int_arith_rule(`0i <= (d:int) ==> 0i <= 1i + d`)), ih);
  thm step = spec_rule(`a:cm_type`,
      conjunct2_rule(conjunct2_rule(
        conjunct2_rule(cm_type_depth_def))));
  thm under = beta_norm(ap_term_rule(`\z:int. 0i <= z`, step));
  ACCEPT_TAC(ptr, eq_mp_rule(sym_rule(under), rhs));
  return gnode_prove(root);
}
PROOF thm cm_type_depth_nonneg = mk_cm_type_depth_nonneg();

PROOF thm mk_cm_type_base_range(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type). cm_type_code_wf ty ==>
         0i <= cm_type_base_code ty &&
         cm_type_base_code ty < 1024i`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < 2; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv,
        THM_LIST(cm_type_code_wf_def, cm_type_base_code_def));
  }
  gnode structure = AUTO_INTROS_TAC(cases[2]);
  thm swf = conv_rule(rewrite_conv(THM_LIST(cm_type_code_wf_def)),
      assume_rule(goal_lasmps(structure->g)[0].tm));
  thm srng = mp_rule(mp_rule(inst_rule(TERM_PAIR_LIST(
      (term_pair){`a:int`, `sid:int`}), int_arith_rule(
        `0i <= (sid:int) ==> sid < 1022i ==>
         0i <= sid + 2i && sid + 2i < 1024i`)),
      conjunct1_rule(swf)), conjunct2_rule(swf));
  gnode structure_reduced = CONV_TAC(structure,
      rewrite_conv(THM_LIST(cm_type_base_code_def)));
  ACCEPT_TAC(structure_reduced, srng);
  gnode ptr = AUTO_INTROS_TAC(cases[3]);
  thm pih = assume_rule(goal_lasmps(ptr->g)[0].tm);
  thm pwf = conv_rule(rewrite_conv(THM_LIST(cm_type_code_wf_def)),
      assume_rule(goal_lasmps(ptr->g)[1].tm));
  thm prng = mp_rule(pih, pwf);
  gnode ptr_reduced = CONV_TAC(ptr,
      rewrite_conv(THM_LIST(cm_type_base_code_def)));
  ACCEPT_TAC(ptr_reduced, prng);
  return gnode_prove(root);
}
PROOF thm cm_type_base_range = mk_cm_type_base_range();
PROOF thm mk_cm_type_base_decode(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type). cm_type_code_wf ty ==>
         cm_type_base_decode (cm_type_base_code ty) ==
         cm_type_strip ty`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < 2; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv,
        THM_LIST(cm_type_code_wf_def, cm_type_base_code_def,
          cm_type_base_decode_def, cm_type_strip_def));
  }
  gnode structure = AUTO_INTROS_TAC(cases[2]);
  thm swf = conv_rule(rewrite_conv(THM_LIST(cm_type_code_wf_def)),
      assume_rule(goal_lasmps(structure->g)[0].tm));
  thm sar = mp_rule(inst_rule(TERM_PAIR_LIST(
      (term_pair){`a:int`, `sid:int`}), int_arith_rule(
        `0i <= (sid:int) ==>
         ~((sid + 2i == 0i)) && ~((sid + 2i == 1i)) &&
         sid + 2i - 2i == sid`)), conjunct1_rule(swf));
  thm sbc = spec_rule(`a:int`, conjunct1_rule(conjunct2_rule(
      conjunct2_rule(cm_type_base_code_def))));
  thm sstrip = spec_rule(`a:int`, conjunct1_rule(conjunct2_rule(
      conjunct2_rule(cm_type_strip_def))));
  thm sdecode = inst_rule(TERM_PAIR_LIST(
      (term_pair){`(a:int) + 2i`, `code:int`}),
      cm_type_base_decode_def);
  thm sdecoded = conv_rule(reduce_rewrite_conv(THM_LIST(sar)), sdecode);
  thm sdecoded_final = conv_rule(rewrite_conv(THM_LIST(
      int_ring_rule(`((a:int) + 2i) - 2i == a`))), sdecoded);
  thm slhs = ap_term_rule(`cm_type_base_decode`,
      sbc);
  ACCEPT_TAC(structure,
      trans_rule(slhs, trans_rule(sdecoded_final, sym_rule(sstrip))));
  gnode ptr = AUTO_INTROS_TAC(cases[3]);
  thm pih = assume_rule(goal_lasmps(ptr->g)[0].tm);
  thm pwf = conv_rule(rewrite_conv(THM_LIST(cm_type_code_wf_def)),
      assume_rule(goal_lasmps(ptr->g)[1].tm));
  thm peq = mp_rule(pih, pwf);
  thm pbc = spec_rule(`a:cm_type`, conjunct2_rule(conjunct2_rule(
      conjunct2_rule(cm_type_base_code_def))));
  thm pstrip = spec_rule(`a:cm_type`, conjunct2_rule(conjunct2_rule(
      conjunct2_rule(cm_type_strip_def))));
  thm plhs = ap_term_rule(`cm_type_base_decode`, pbc);
  ACCEPT_TAC(ptr,
      trans_rule(plhs, trans_rule(peq, sym_rule(pstrip))));
  return gnode_prove(root);
}
PROOF thm cm_type_base_decode = mk_cm_type_base_decode();

PROOF thm mk_cm_add_ptrs_depth(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_add_ptrs (num_of_int (cm_type_depth ty))
           (cm_type_strip ty) == ty`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < 3; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_TAC(leaf, reduce_rewrite_conv(
        THM_LIST(cm_type_depth_def, cm_type_strip_def,
          cm_add_ptrs_def,
          spec_rule(`0:num`,
            get_theorem_by_name("NUM_OF_INT_OF_NUM")))));
  }
  gnode ptr = AUTO_INTROS_TAC(cases[3]);
  thm ih = assume_rule(goal_lasmps(ptr->g)[0].tm);
  thm depth_step = spec_rule(`a:cm_type`,
      conjunct2_rule(conjunct2_rule(
        conjunct2_rule(cm_type_depth_def))));
  thm strip_step = spec_rule(`a:cm_type`,
      conjunct2_rule(conjunct2_rule(
        conjunct2_rule(cm_type_strip_def))));
  thm idx0 = ap_term_rule(`num_of_int`, depth_step);
  thm idx1 = ap_term_rule(`num_of_int`,
      int_ring_rule(`1i + cm_type_depth (a:cm_type) ==
                     cm_type_depth a + 1i`));
  thm depth_nonneg = spec_rule(`a:cm_type`, cm_type_depth_nonneg);
  thm noa = spec_rule(`1i:int`, spec_rule(
      `cm_type_depth (a:cm_type)`,
      get_theorem_by_name("NUM_OF_INT_ADD")));
  thm noa2 = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("NUM_OF_INT_OF_NUM"))), noa);
  thm add_eq = mp_rule(noa2,
      conj_rule(depth_nonneg, int_arith_rule(`0i <= 1i`)));
  thm add1 = spec_rule(`num_of_int (cm_type_depth (a:cm_type))`,
      get_theorem_by_name("ADD1"));
  thm idx2 = trans_rule(add_eq, sym_rule(add1));
  thm idx = trans_rule(idx0, trans_rule(idx1, idx2));
  thm lhs = mk_comb_rule(mk_comb_rule(
      refl_rule(`cm_add_ptrs:num->cm_type->cm_type`), idx), strip_step);
  thm add_step = specl_rule(TERM_LIST(
      `num_of_int (cm_type_depth (a:cm_type))`,
      `cm_type_strip (a:cm_type)`), conjunct2_rule(cm_add_ptrs_def));
  thm lift_ih = ap_term_rule(`CMPtrTy`, ih);
  ACCEPT_TAC(ptr, trans_rule(lhs, trans_rule(add_step, lift_ih)));
  return gnode_prove(root);
}
PROOF thm cm_add_ptrs_depth = mk_cm_add_ptrs_depth();

PROOF thm mk_cm_type_encode_divmod(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type). cm_type_code_wf ty ==>
         cm_type_encode ty / 1024i == cm_type_depth ty &&
         cm_type_encode ty % 1024i == cm_type_base_code ty`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm hwf = assume_rule(goal_lasmps(leaf->g)[0].tm);
  thm rng = mp_rule(spec_rule(`ty:cm_type`, cm_type_base_range), hwf);
  thm enc = inst_rule(TERM_PAIR_LIST(
      (term_pair){`ty:cm_type`, `ty:cm_type`}), cm_type_encode_def);
  thm reorder = int_ring_rule(
      `1024i * cm_type_depth (ty:cm_type) +
         cm_type_base_code ty ==
       cm_type_depth ty * 1024i + cm_type_base_code ty`);
  thm decomposition = trans_rule(enc, reorder);
  thm abs_eq = spec_rule(`1024:num`,
      get_theorem_by_name("INT_ABS_NUM"));
  thm under_abs = beta_norm(ap_term_rule(
      `\z:int. cm_type_base_code (ty:cm_type) < z`, abs_eq));
  thm upper_abs =
      eq_mp_rule(sym_rule(under_abs), conjunct2_rule(rng));
  thm divmod = specl_rule(TERM_LIST(
      `cm_type_encode (ty:cm_type)`, `1024i`,
      `cm_type_depth (ty:cm_type)`,
      `cm_type_base_code (ty:cm_type)`),
      get_theorem_by_name("INT_DIVMOD_UNIQ"));
  ACCEPT_TAC(leaf, mp_rule(divmod,
      conj_rule(decomposition,
        conj_rule(conjunct1_rule(rng), upper_abs))));
  return gnode_prove(root);
}
PROOF thm cm_type_encode_divmod = mk_cm_type_encode_divmod();

PROOF thm mk_cm_type_roundtrip(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type). cm_type_code_wf ty ==>
         cm_type_decode (cm_type_encode ty) == ty`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm hwf = assume_rule(goal_lasmps(leaf->g)[0].tm);
  thm divmod =
      mp_rule(spec_rule(`ty:cm_type`, cm_type_encode_divmod), hwf);
  thm base =
      mp_rule(spec_rule(`ty:cm_type`, cm_type_base_decode), hwf);
  thm decoded = inst_rule(TERM_PAIR_LIST(
      (term_pair){`cm_type_encode (ty:cm_type)`, `code:int`}),
      cm_type_decode_def);
  thm reduced = conv_rule(rewrite_conv(THM_LIST(
      conjunct1_rule(divmod), conjunct2_rule(divmod), base)), decoded);
  thm rebuilt = spec_rule(`ty:cm_type`, cm_add_ptrs_depth);
  ACCEPT_TAC(leaf, trans_rule(reduced, rebuilt));
  return gnode_prove(root);
}
PROOF thm cm_type_roundtrip = mk_cm_type_roundtrip();

PROOF thm get_cm_type_depth_def(void) { return cm_type_depth_def; }
PROOF thm get_cm_type_base_code_def(void) { return cm_type_base_code_def; }
PROOF thm get_cm_type_code_wf_def(void) {
  return cm_type_code_wf_def;
}
PROOF thm get_cm_type_depth_nonneg(void) {
  return cm_type_depth_nonneg;
}
PROOF thm get_cm_type_base_range(void) {
  return cm_type_base_range;
}
PROOF thm get_cm_type_encode_def(void) { return cm_type_encode_def; }
PROOF thm get_cm_type_encode_divmod(void) {
  return cm_type_encode_divmod;
}
PROOF thm get_cm_type_decode_def(void) { return cm_type_decode_def; }
PROOF thm get_cm_type_roundtrip(void) { return cm_type_roundtrip; }

/* --------------------------------------------------------------------- */
/* Resolved typing.  Constructor payloads are already shape-canonical;   */
/* these predicates validate dense references and every stored type.      */
/* --------------------------------------------------------------------- */

PROOF thm cm_type_refs_def = new_rec_definition(cm_type_RECURSION,
    `(cm_type_refs (structs:(cm_struct_d)list) CMIntTy = T) &&
     (cm_type_refs structs CMCharTy = T) &&
     (!sid. cm_type_refs structs (CMStructTy (sid:int)) <=>
        0i <= sid && sid < ilength structs) &&
     (!ty. cm_type_refs structs (CMPtrTy (ty:cm_type)) <=>
        cm_type_refs structs ty)`);
PROOF int _e_cm_type_refs = cst_add_const_to_header(`cm_type_refs`);

PROOF thm cm_is_pointer_def = new_rec_definition(cm_type_RECURSION,
    `(cm_is_pointer CMIntTy = F) &&
     (cm_is_pointer CMCharTy = F) &&
     (!sid. cm_is_pointer (CMStructTy (sid:int)) = F) &&
     (!ty. cm_is_pointer (CMPtrTy (ty:cm_type)) = T)`);
PROOF thm cm_is_struct_def = new_rec_definition(cm_type_RECURSION,
    `(cm_is_struct CMIntTy = F) &&
     (cm_is_struct CMCharTy = F) &&
     (!sid. cm_is_struct (CMStructTy (sid:int)) = T) &&
     (!ty. cm_is_struct (CMPtrTy (ty:cm_type)) = F)`);
PROOF thm cm_pointee_def = new_rec_definition(cm_type_RECURSION,
    `(cm_pointee CMIntTy = CMIntTy) &&
     (cm_pointee CMCharTy = CMCharTy) &&
     (!sid. cm_pointee (CMStructTy (sid:int)) = CMStructTy sid) &&
     (!ty. cm_pointee (CMPtrTy (ty:cm_type)) = ty)`);
PROOF thm cm_struct_id_def = new_rec_definition(cm_type_RECURSION,
    `(cm_struct_id CMIntTy = --1i) &&
     (cm_struct_id CMCharTy = --1i) &&
     (!sid. cm_struct_id (CMStructTy (sid:int)) = sid) &&
     (!ty. cm_struct_id (CMPtrTy (ty:cm_type)) =
        cm_struct_id ty)`);
PROOF int _e_cm_is_pointer = cst_add_const_to_header(`cm_is_pointer`);
PROOF int _e_cm_is_struct = cst_add_const_to_header(`cm_is_struct`);
PROOF int _e_cm_pointee = cst_add_const_to_header(`cm_pointee`);
PROOF int _e_cm_struct_id = cst_add_const_to_header(`cm_struct_id`);

PROOF thm cm_scalar_type_def = new_fun_definition(
    `cm_scalar_type (structs:(cm_struct_d)list) (ty:cm_type) : bool =
       (cm_type_code_wf ty && cm_type_refs structs ty &&
        ~(cm_is_struct ty))`);
PROOF int _e_cm_scalar_type = cst_add_const_to_header(`cm_scalar_type`);

PROOF thm cm_slot_expr_type_def = new_fun_definition(
    `cm_slot_expr_type (slot:cm_slot_d) : cm_type =
       (if cm_slot_count slot == 0i
        then cm_slot_ty slot
        else CMPtrTy (cm_slot_ty slot))`);
PROOF int _e_cm_slot_expr_type =
    cst_add_const_to_header(`cm_slot_expr_type`);

PROOF thm cm_global_expr_type_def = new_fun_definition(
    `cm_global_expr_type (g:cm_global_d) : cm_type =
       (if cm_global_count g == 0i
        then cm_global_ty g
        else CMPtrTy (cm_global_ty g))`);
PROOF int _e_cm_global_expr_type =
    cst_add_const_to_header(`cm_global_expr_type`);

PROOF thm cm_convertible_def = new_fun_definition(
    `cm_convertible (from:cm_type) (to:cm_type) : bool =
       (~(cm_is_struct from) && ~(cm_is_struct to) &&
        (from == to ||
         ((from == CMIntTy || from == CMCharTy) &&
          (to == CMIntTy || to == CMCharTy)) ||
         (cm_is_pointer from && cm_is_pointer to &&
          (from == CMPtrTy CMCharTy || to == CMPtrTy CMCharTy))))`);
PROOF int _e_cm_convertible = cst_add_const_to_header(`cm_convertible`);

PROOF thm cm_expr_type_def = new_rec_definition(cm_expr_RECURSION,
    `(cm_expr_type (CMConstE (n:int) (ty:cm_type)) = ty) &&
     (cm_expr_type (CMStringE (sid:int) (ty:cm_type)) = ty) &&
     (cm_expr_type
        (CMVarE (scope:int) (slot:int) (ty:cm_type)) = ty) &&
     (!dst src ty.
        cm_expr_type
          (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) = ty) &&
     (!op left right ty.
        cm_expr_type
          (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
             (ty:cm_type)) = ty) &&
     (!op arg ty.
        cm_expr_type
          (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) = ty) &&
     (!base index ty.
        cm_expr_type
          (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) = ty) &&
     (!base mid ty.
        cm_expr_type
          (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) = ty) &&
     (!fid args ty.
        cm_expr_type
          (CMCallE (fid:int) (args:(cm_expr)list) (ty:cm_type)) = ty) &&
     (!asked ty.
        cm_expr_type
          (CMSizeofE (asked:cm_type) (ty:cm_type)) = ty) &&
     (!ty. cm_expr_type (CMGetcE (ty:cm_type)) = ty) &&
     (!arg ty. cm_expr_type (CMPutcE (arg:cm_expr) (ty:cm_type)) = ty) &&
     (!arg ty. cm_expr_type (CMPutiE (arg:cm_expr) (ty:cm_type)) = ty) &&
     (!arg ty. cm_expr_type (CMExitE (arg:cm_expr) (ty:cm_type)) = ty) &&
     (cm_expr_list_type ([]:(cm_expr)list) = CMIntTy) &&
     (!arg args.
        cm_expr_list_type
          ((arg:cm_expr) :: (args:(cm_expr)list)) =
        cm_expr_type arg)`);
PROOF int _e_cm_expr_type = cst_add_const_to_header(`cm_expr_type`);

PROOF thm cm_integer_type_def = new_fun_definition(
    `cm_integer_type (ty:cm_type) : bool =
       (ty == CMIntTy || ty == CMCharTy)`);
PROOF thm cm_scalar_expr_type_def = new_fun_definition(
    `cm_scalar_expr_type (ty:cm_type) : bool =
       (cm_integer_type ty || cm_is_pointer ty)`);
PROOF thm cm_zero_literal_def = new_fun_definition(
    `cm_zero_literal (expr:cm_expr) : bool =
       (expr == CMConstE 0i CMIntTy)`);
PROOF thm cm_expr_convertible_def = new_fun_definition(
    `cm_expr_convertible (expr:cm_expr) (to:cm_type) : bool =
       (cm_convertible (cm_expr_type expr) to ||
        (cm_is_pointer to && cm_zero_literal expr))`);
PROOF int _e_cm_integer_type =
    cst_add_const_to_header(`cm_integer_type`);
PROOF int _e_cm_scalar_expr_type =
    cst_add_const_to_header(`cm_scalar_expr_type`);
PROOF int _e_cm_zero_literal =
    cst_add_const_to_header(`cm_zero_literal`);
PROOF int _e_cm_expr_convertible =
    cst_add_const_to_header(`cm_expr_convertible`);

PROOF thm cm_lvalue_def = new_rec_definition(cm_expr_RECURSION,
    `(cm_lvalue (CMConstE (n:int) (ty:cm_type)) = F) &&
     (cm_lvalue (CMStringE (sid:int) (ty:cm_type)) = F) &&
     (cm_lvalue (CMVarE (scope:int) (slot:int) (ty:cm_type)) = T) &&
     (!dst src ty.
        cm_lvalue
          (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) = F) &&
     (!op left right ty.
        cm_lvalue
          (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
             (ty:cm_type)) = F) &&
     (!op arg ty.
        cm_lvalue
          (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) <=>
        op == 2i) &&
     (!base index ty.
        cm_lvalue
          (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) = T) &&
     (!base mid ty.
        cm_lvalue
          (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) = T) &&
     (!fid args ty.
        cm_lvalue
          (CMCallE (fid:int) (args:(cm_expr)list) (ty:cm_type)) = F) &&
     (!asked ty.
        cm_lvalue
          (CMSizeofE (asked:cm_type) (ty:cm_type)) = F) &&
     (!ty. cm_lvalue (CMGetcE (ty:cm_type)) = F) &&
     (!arg ty. cm_lvalue (CMPutcE (arg:cm_expr) (ty:cm_type)) = F) &&
     (!arg ty. cm_lvalue (CMPutiE (arg:cm_expr) (ty:cm_type)) = F) &&
     (!arg ty. cm_lvalue (CMExitE (arg:cm_expr) (ty:cm_type)) = F) &&
     (cm_lvalue_list ([]:(cm_expr)list) = F) &&
     (!arg args.
        cm_lvalue_list
          ((arg:cm_expr) :: (args:(cm_expr)list)) =
        cm_lvalue arg)`);
PROOF int _e_cm_lvalue = cst_add_const_to_header(`cm_lvalue`);

PROOF thm cm_binding_type_def = new_fun_definition(
    `cm_binding_type (p:cm_program) (f:cm_function_d)
       (scope:int) (slot:int) : cm_type =
       (if scope == 0i
        then cm_global_expr_type
               (inth slot (cm_program_globals p))
        else if scope == 1i
             then cm_slot_expr_type
                    (inth slot (cm_function_locals f))
             else cm_slot_expr_type
                    (inth slot (cm_function_params f)))`);
PROOF int _e_cm_binding_type = cst_add_const_to_header(`cm_binding_type`);

PROOF thm cm_binding_valid_def = new_fun_definition(
    `cm_binding_valid (p:cm_program) (f:cm_function_d)
       (scope:int) (slot:int) : bool =
       ((scope == 0i && 0i <= slot &&
         slot < ilength (cm_program_globals p)) ||
        (scope == 1i && 0i <= slot &&
         slot < ilength (cm_function_locals f)) ||
        (scope == 2i && 0i <= slot &&
         slot < ilength (cm_function_params f)))`);
PROOF int _e_cm_binding_valid =
    cst_add_const_to_header(`cm_binding_valid`);

PROOF thm cm_binary_types_def = new_fun_definition(
    `cm_binary_types (op:int) (left:cm_type) (right:cm_type)
       (result:cm_type) : bool =
       (0i <= op && op <= 12i &&
        (if op == 0i || op == 1i
         then cm_scalar_expr_type left && cm_scalar_expr_type right &&
              result == CMIntTy
         else if 2i <= op && op <= 7i
              then result == CMIntTy &&
                   ((cm_integer_type left && cm_integer_type right) ||
                    (cm_is_pointer left && left == right))
         else if op == 8i
              then ((cm_integer_type left && cm_integer_type right &&
                     result == CMIntTy) ||
                    (cm_is_pointer left && cm_integer_type right &&
                     result == left) ||
                    (cm_is_pointer right && cm_integer_type left &&
                     result == right))
         else if op == 9i
              then ((cm_integer_type left && cm_integer_type right &&
                     result == CMIntTy) ||
                    (cm_is_pointer left && cm_integer_type right &&
                     result == left) ||
                    (left == right && cm_is_pointer left &&
                     result == CMIntTy))
         else cm_integer_type left && cm_integer_type right &&
              result == CMIntTy))`);
PROOF int _e_cm_binary_types =
    cst_add_const_to_header(`cm_binary_types`);

PROOF thm cm_unary_types_def = new_fun_definition(
    `cm_unary_types (op:int) (arg:cm_type) (result:cm_type) : bool =
       (0i <= op && op <= 3i &&
        (if op == 0i || op == 1i
         then (arg == CMIntTy || arg == CMCharTy) &&
              result == CMIntTy
         else if op == 2i
              then cm_is_pointer arg && result == cm_pointee arg
              else result == CMPtrTy arg))`);
PROOF int _e_cm_unary_types = cst_add_const_to_header(`cm_unary_types`);

PROOF thm cm_member_type_def = new_fun_definition(
    `cm_member_type (p:cm_program) (base:cm_type) (mid:int) : cm_type =
       cm_slot_expr_type
         (inth mid (cm_struct_members
           (inth (cm_struct_id (cm_pointee base))
             (cm_program_structs p))))`);
PROOF int _e_cm_member_type = cst_add_const_to_header(`cm_member_type`);

PROOF thm cm_member_valid_def = new_fun_definition(
    `cm_member_valid (p:cm_program) (base:cm_type) (mid:int) : bool =
       (cm_is_pointer base &&
        cm_is_struct (cm_pointee base) &&
        0i <= cm_struct_id (cm_pointee base) &&
        cm_struct_id (cm_pointee base) <
          ilength (cm_program_structs p) &&
        0i <= mid &&
        mid < ilength (cm_struct_members
          (inth (cm_struct_id (cm_pointee base))
            (cm_program_structs p))))`);
PROOF int _e_cm_member_valid = cst_add_const_to_header(`cm_member_valid`);

PROOF thm cm_expr_array_def = new_rec_definition(cm_expr_RECURSION,
    `(cm_expr_array (p:cm_program) (f:cm_function_d)
        (CMConstE (n:int) (ty:cm_type)) = F) &&
     (cm_expr_array p f (CMStringE (sid:int) (ty:cm_type)) = F) &&
     (cm_expr_array p f
        (CMVarE (scope:int) (slot:int) (ty:cm_type)) =
        (if scope == 0i
         then ~(cm_global_count
                  (inth slot (cm_program_globals p)) == 0i)
         else if scope == 1i
              then ~(cm_slot_count
                (inth slot (cm_function_locals f)) == 0i)
              else F)) &&
     (!dst src ty.
        cm_expr_array p f
          (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) = F) &&
     (!op left right ty.
        cm_expr_array p f
          (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
            (ty:cm_type)) = F) &&
     (!op arg ty.
        cm_expr_array p f
          (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) = F) &&
     (!base index ty.
        cm_expr_array p f
          (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) = F) &&
     (!base mid ty.
        cm_expr_array p f
          (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) =
        ~(cm_slot_count
            (inth mid
              (cm_struct_members
                (inth (cm_struct_id
                        (cm_pointee (cm_expr_type base)))
                  (cm_program_structs p)))) == 0i)) &&
     (!fid args ty.
        cm_expr_array p f
          (CMCallE (fid:int) (args:(cm_expr)list) (ty:cm_type)) = F) &&
     (!asked ty.
        cm_expr_array p f
          (CMSizeofE (asked:cm_type) (ty:cm_type)) = F) &&
     (!ty. cm_expr_array p f (CMGetcE (ty:cm_type)) = F) &&
     (!arg ty.
        cm_expr_array p f
          (CMPutcE (arg:cm_expr) (ty:cm_type)) = F) &&
     (!arg ty.
        cm_expr_array p f
          (CMPutiE (arg:cm_expr) (ty:cm_type)) = F) &&
     (!arg ty.
        cm_expr_array p f
          (CMExitE (arg:cm_expr) (ty:cm_type)) = F)`);
PROOF int _e_cm_expr_array =
    cst_add_const_to_header(`cm_expr_array`);

PROOF thm cm_expr_wf_def = new_rec_definition(cm_expr_RECURSION,
    `(cm_expr_wf (p:cm_program) (f:cm_function_d)
        (CMConstE (n:int) (ty:cm_type)) <=>
        cm_integer_type ty) &&
     (cm_expr_wf p f
        (CMStringE (sid:int) (ty:cm_type)) <=>
        0i <= sid && sid < ilength (cm_program_strings p) &&
        ty == CMPtrTy CMCharTy) &&
     (cm_expr_wf p f
        (CMVarE (scope:int) (slot:int) (ty:cm_type)) <=>
        cm_binding_valid p f scope slot &&
        ty == cm_binding_type p f scope slot) &&
     (!dst src ty.
        cm_expr_wf p f
          (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) <=>
        cm_expr_wf p f dst && cm_expr_wf p f src &&
        cm_lvalue dst && ~cm_expr_array p f dst &&
        ty == cm_expr_type dst &&
        cm_expr_convertible src ty) &&
     (!op left right ty.
        cm_expr_wf p f
          (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
             (ty:cm_type)) <=>
        cm_expr_wf p f left && cm_expr_wf p f right &&
        cm_binary_types op (cm_expr_type left)
          (cm_expr_type right) ty) &&
     (!op arg ty.
        cm_expr_wf p f
          (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) <=>
        cm_expr_wf p f arg &&
        cm_unary_types op (cm_expr_type arg) ty &&
        (op == 3i ==>
          (cm_lvalue arg && ~cm_expr_array p f arg))) &&
     (!base index ty.
        cm_expr_wf p f
          (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) <=>
        cm_expr_wf p f base && cm_expr_wf p f index &&
        cm_is_pointer (cm_expr_type base) &&
        (cm_expr_type index == CMIntTy ||
         cm_expr_type index == CMCharTy) &&
        ty == cm_pointee (cm_expr_type base)) &&
     (!base mid ty.
        cm_expr_wf p f
          (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) <=>
        cm_expr_wf p f base &&
        cm_member_valid p (cm_expr_type base) mid &&
        ty == cm_member_type p (cm_expr_type base) mid) &&
     (!fid args ty.
        cm_expr_wf p f
          (CMCallE (fid:int) (args:(cm_expr)list) (ty:cm_type)) <=>
        0i <= fid && fid < ilength (cm_program_functions p) &&
        cm_args_wf p f args
          (cm_function_params
            (inth fid (cm_program_functions p))) &&
        ty == cm_function_ret
          (inth fid (cm_program_functions p))) &&
     (!asked ty.
        cm_expr_wf p f
          (CMSizeofE (asked:cm_type) (ty:cm_type)) <=>
        cm_type_code_wf asked &&
        cm_type_refs (cm_program_structs p) asked &&
        ty == CMIntTy) &&
     (!ty. cm_expr_wf p f (CMGetcE (ty:cm_type)) <=>
        ty == CMIntTy) &&
     (!arg ty.
        cm_expr_wf p f (CMPutcE (arg:cm_expr) (ty:cm_type)) <=>
        cm_expr_wf p f arg &&
        cm_scalar_type (cm_program_structs p) (cm_expr_type arg) &&
        ty == CMIntTy) &&
     (!arg ty.
        cm_expr_wf p f (CMPutiE (arg:cm_expr) (ty:cm_type)) <=>
        cm_expr_wf p f arg &&
        (cm_expr_type arg == CMIntTy ||
         cm_expr_type arg == CMCharTy) &&
        ty == CMIntTy) &&
     (!arg ty.
        cm_expr_wf p f (CMExitE (arg:cm_expr) (ty:cm_type)) <=>
        cm_expr_wf p f arg &&
        (cm_expr_type arg == CMIntTy ||
         cm_expr_type arg == CMCharTy) &&
        ty == CMIntTy) &&
     (cm_args_wf (p:cm_program) (f:cm_function_d)
        ([]:(cm_expr)list) (slots:(cm_slot_d)list) <=>
        slots == []) &&
     (!arg args slots.
        cm_args_wf p f
          ((arg:cm_expr) :: (args:(cm_expr)list))
          (slots:(cm_slot_d)list) <=>
        ~(slots == []) &&
        cm_expr_wf p f arg &&
        cm_expr_convertible arg (cm_slot_ty (HD slots)) &&
        cm_args_wf p f args (TL slots))`);
PROOF int _e_cm_expr_wf = cst_add_const_to_header(`cm_expr_wf`);
PROOF int _e_cm_args_wf = cst_add_const_to_header(`cm_args_wf`);

PROOF thm cm_decl_count_def = new_rec_definition(cm_stmt_RECURSION,
    `(cm_decl_count (slot:int) CMSkipS = 0i) &&
     (!expr. cm_decl_count slot (CMExprS (expr:cm_expr)) = 0i) &&
     (!decl.
        cm_decl_count slot (CMDeclS (decl:int)) =
        (if decl == slot then 1i else 0i)) &&
     (!decl expr.
        cm_decl_count slot (CMInitS (decl:int) (expr:cm_expr)) =
        (if decl == slot then 1i else 0i)) &&
     (!first second.
        cm_decl_count slot
          (CMSeqS (first:cm_stmt) (second:cm_stmt)) =
        cm_decl_count slot first + cm_decl_count slot second) &&
     (!body.
        cm_decl_count slot (CMBlockS (body:cm_stmt)) =
        cm_decl_count slot body) &&
     (!guard yes no.
        cm_decl_count slot
          (CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)) =
        cm_decl_count slot yes + cm_decl_count slot no) &&
     (!guard body.
        cm_decl_count slot
          (CMWhileS (guard:cm_expr) (body:cm_stmt)) =
        cm_decl_count slot body) &&
     (cm_decl_count slot CMBreakS = 0i) &&
     (cm_decl_count slot CMContinueS = 0i) &&
     (!expr. cm_decl_count slot (CMReturnS (expr:cm_expr)) = 0i)`);
PROOF int _e_cm_decl_count = cst_add_const_to_header(`cm_decl_count`);

PROOF thm cm_stmt_wf_def = new_rec_definition(cm_stmt_RECURSION,
    `(cm_stmt_wf (p:cm_program) (f:cm_function_d)
        (loop:bool) CMSkipS = T) &&
     (!expr.
        cm_stmt_wf p f loop (CMExprS (expr:cm_expr)) <=>
        cm_expr_wf p f expr &&
        cm_scalar_expr_type (cm_expr_type expr)) &&
     (!slot.
        cm_stmt_wf p f loop (CMDeclS (slot:int)) <=>
        0i <= slot && slot < ilength (cm_function_locals f)) &&
     (!slot expr.
        cm_stmt_wf p f loop
          (CMInitS (slot:int) (expr:cm_expr)) <=>
        0i <= slot && slot < ilength (cm_function_locals f) &&
        cm_slot_count (inth slot (cm_function_locals f)) == 0i &&
        cm_expr_wf p f expr &&
        cm_expr_convertible expr
          (cm_slot_ty (inth slot (cm_function_locals f)))) &&
     (!first second.
        cm_stmt_wf p f loop
          (CMSeqS (first:cm_stmt) (second:cm_stmt)) <=>
        cm_stmt_wf p f loop first &&
        cm_stmt_wf p f loop second) &&
     (!body.
        cm_stmt_wf p f loop (CMBlockS (body:cm_stmt)) <=>
        cm_stmt_wf p f loop body) &&
     (!guard yes no.
        cm_stmt_wf p f loop
          (CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)) <=>
        cm_expr_wf p f guard &&
        (cm_expr_type guard == CMIntTy ||
         cm_expr_type guard == CMCharTy ||
         cm_is_pointer (cm_expr_type guard)) &&
        cm_stmt_wf p f loop yes &&
        cm_stmt_wf p f loop no) &&
     (!guard body.
        cm_stmt_wf p f loop
          (CMWhileS (guard:cm_expr) (body:cm_stmt)) <=>
        cm_expr_wf p f guard &&
        (cm_expr_type guard == CMIntTy ||
         cm_expr_type guard == CMCharTy ||
         cm_is_pointer (cm_expr_type guard)) &&
        cm_stmt_wf p f T body) &&
     (cm_stmt_wf p f loop CMBreakS <=> loop) &&
     (cm_stmt_wf p f loop CMContinueS <=> loop) &&
     (!expr.
        cm_stmt_wf p f loop (CMReturnS (expr:cm_expr)) <=>
        cm_expr_wf p f expr &&
        cm_expr_convertible expr (cm_function_ret f))`);
PROOF int _e_cm_stmt_wf = cst_add_const_to_header(`cm_stmt_wf`);

PROOF thm cm_slot_wf_def = new_fun_definition(
    `cm_slot_wf (structs:(cm_struct_d)list) (slot:cm_slot_d) : bool =
       (0i <= cm_slot_count slot &&
        cm_scalar_type structs (cm_slot_ty slot) &&
        0i < cm_slot_size structs slot &&
        cm_slot_size structs slot <= 1048576i)`);
PROOF int _e_cm_slot_wf = cst_add_const_to_header(`cm_slot_wf`);

PROOF thm cm_slots_wf_def = new_fun_definition(
    `cm_slots_wf (structs:(cm_struct_d)list)
       (slots:(cm_slot_d)list) : bool =
       (!i. 0i <= i ==> i < ilength slots ==>
            cm_slot_wf structs (inth i slots))`);
PROOF int _e_cm_slots_wf = cst_add_const_to_header(`cm_slots_wf`);

PROOF thm cm_params_wf_def = new_fun_definition(
    `cm_params_wf (structs:(cm_struct_d)list)
       (slots:(cm_slot_d)list) : bool =
       (cm_slots_wf structs slots &&
        (!i. 0i <= i ==> i < ilength slots ==>
             cm_slot_count (inth i slots) == 0i))`);
PROOF int _e_cm_params_wf = cst_add_const_to_header(`cm_params_wf`);

PROOF thm cm_struct_wf_def = new_fun_definition(
    `cm_struct_wf (structs:(cm_struct_d)list)
       (s:cm_struct_d) : bool =
       (~(cm_struct_members s == []) &&
        cm_slots_wf structs (cm_struct_members s) &&
        0i < cm_struct_slots_size (cm_struct_members s) &&
        cm_struct_slots_size (cm_struct_members s) <= 1048576i)`);
PROOF int _e_cm_struct_wf = cst_add_const_to_header(`cm_struct_wf`);

PROOF thm cm_global_wf_def = new_fun_definition(
    `cm_global_wf (structs:(cm_struct_d)list)
       (g:cm_global_d) : bool =
       (0i <= cm_global_count g &&
        cm_scalar_type structs (cm_global_ty g) &&
        0i < cm_global_size structs g &&
        cm_global_size structs g <= 1048576i &&
        (cm_global_has_init g ==> cm_global_count g == 0i) &&
        (cm_global_has_init g ==>
          tower_signed64 (cm_global_init g)) &&
        (cm_global_has_init g && cm_is_pointer (cm_global_ty g) ==>
          cm_global_init g == 0i))`);
PROOF int _e_cm_global_wf = cst_add_const_to_header(`cm_global_wf`);

PROOF thm cm_string_wf_def = new_fun_definition(
    `cm_string_wf (s:cm_string_d) : bool =
       (!i. 0i <= i ==> i < ilength (cm_string_bytes s) ==>
            tower_byte_value (inth i (cm_string_bytes s)))`);
PROOF int _e_cm_string_wf = cst_add_const_to_header(`cm_string_wf`);

PROOF thm cm_expr_scope_wf_def =
  new_rec_definition(cm_expr_RECURSION,
    `(cm_expr_scope_wf (active:int->bool)
        (CMConstE (n:int) (ty:cm_type)) = T) &&
     (cm_expr_scope_wf active
        (CMStringE (sid:int) (ty:cm_type)) = T) &&
     (cm_expr_scope_wf active
        (CMVarE (scope:int) (slot:int) (ty:cm_type)) <=>
        ~(scope == 1i) || active slot) &&
     (!dst src ty.
        cm_expr_scope_wf active
          (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) <=>
        cm_expr_scope_wf active dst && cm_expr_scope_wf active src) &&
     (!op left right ty.
        cm_expr_scope_wf active
          (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
            (ty:cm_type)) <=>
        cm_expr_scope_wf active left &&
        cm_expr_scope_wf active right) &&
     (!op arg ty.
        cm_expr_scope_wf active
          (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) <=>
        cm_expr_scope_wf active arg) &&
     (!base index ty.
        cm_expr_scope_wf active
          (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) <=>
        cm_expr_scope_wf active base &&
        cm_expr_scope_wf active index) &&
     (!base mid ty.
        cm_expr_scope_wf active
          (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) <=>
        cm_expr_scope_wf active base) &&
     (!fid args ty.
        cm_expr_scope_wf active
          (CMCallE (fid:int) (args:(cm_expr)list) (ty:cm_type)) <=>
        cm_expr_list_scope_wf active args) &&
     (!asked ty.
        cm_expr_scope_wf active
          (CMSizeofE (asked:cm_type) (ty:cm_type)) = T) &&
     (!ty. cm_expr_scope_wf active (CMGetcE (ty:cm_type)) = T) &&
     (!arg ty.
        cm_expr_scope_wf active
          (CMPutcE (arg:cm_expr) (ty:cm_type)) <=>
        cm_expr_scope_wf active arg) &&
     (!arg ty.
        cm_expr_scope_wf active
          (CMPutiE (arg:cm_expr) (ty:cm_type)) <=>
        cm_expr_scope_wf active arg) &&
     (!arg ty.
        cm_expr_scope_wf active
          (CMExitE (arg:cm_expr) (ty:cm_type)) <=>
        cm_expr_scope_wf active arg) &&
     (cm_expr_list_scope_wf active ([]:(cm_expr)list) = T) &&
     (!arg args.
        cm_expr_list_scope_wf active
          ((arg:cm_expr) :: (args:(cm_expr)list)) <=>
        cm_expr_scope_wf active arg &&
        cm_expr_list_scope_wf active args)`);
PROOF int _e_cm_expr_scope_wf =
    cst_add_const_to_header(`cm_expr_scope_wf`);
PROOF int _e_cm_expr_list_scope_wf =
    cst_add_const_to_header(`cm_expr_list_scope_wf`);

PROOF thm cm_scope_add_def = new_fun_definition(
    `cm_scope_add (active:int->bool) (slot:int) : int->bool =
       (\i:int. i == slot || active i)`);
PROOF int _e_cm_scope_add = cst_add_const_to_header(`cm_scope_add`);

PROOF thm cm_stmt_scope_result_def =
  new_rec_definition(cm_stmt_RECURSION,
    `(cm_stmt_scope_result (active:int->bool) CMSkipS = active) &&
     (!expr.
        cm_stmt_scope_result active (CMExprS (expr:cm_expr)) = active) &&
     (!slot.
        cm_stmt_scope_result active (CMDeclS (slot:int)) =
          cm_scope_add active slot) &&
     (!slot expr.
        cm_stmt_scope_result active
          (CMInitS (slot:int) (expr:cm_expr)) =
          cm_scope_add active slot) &&
     (!first second.
        cm_stmt_scope_result active
          (CMSeqS (first:cm_stmt) (second:cm_stmt)) =
        cm_stmt_scope_result
          (cm_stmt_scope_result active first) second) &&
     (!body.
        cm_stmt_scope_result active (CMBlockS (body:cm_stmt)) = active) &&
     (!guard yes no.
        cm_stmt_scope_result active
          (CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)) = active) &&
     (!guard body.
        cm_stmt_scope_result active
          (CMWhileS (guard:cm_expr) (body:cm_stmt)) = active) &&
     (cm_stmt_scope_result active CMBreakS = active) &&
     (cm_stmt_scope_result active CMContinueS = active) &&
     (!expr.
        cm_stmt_scope_result active (CMReturnS (expr:cm_expr)) = active)`);
PROOF int _e_cm_stmt_scope_result =
    cst_add_const_to_header(`cm_stmt_scope_result`);

PROOF thm cm_stmt_scope_wf_def =
  new_rec_definition(cm_stmt_RECURSION,
    `(cm_stmt_scope_wf (active:int->bool) CMSkipS = T) &&
     (!expr.
        cm_stmt_scope_wf active (CMExprS (expr:cm_expr)) <=>
        cm_expr_scope_wf active expr) &&
     (!slot.
        cm_stmt_scope_wf active (CMDeclS (slot:int)) <=>
        ~(active slot)) &&
     (!slot expr.
        cm_stmt_scope_wf active
          (CMInitS (slot:int) (expr:cm_expr)) <=>
        ~(active slot) && cm_expr_scope_wf active expr) &&
     (!first second.
        cm_stmt_scope_wf active
          (CMSeqS (first:cm_stmt) (second:cm_stmt)) <=>
        cm_stmt_scope_wf active first &&
        cm_stmt_scope_wf (cm_stmt_scope_result active first) second) &&
     (!body.
        cm_stmt_scope_wf active (CMBlockS (body:cm_stmt)) <=>
        cm_stmt_scope_wf active body) &&
     (!guard yes no.
        cm_stmt_scope_wf active
          (CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)) <=>
        cm_expr_scope_wf active guard &&
        cm_stmt_scope_wf active yes &&
        cm_stmt_scope_wf active no) &&
     (!guard body.
        cm_stmt_scope_wf active
          (CMWhileS (guard:cm_expr) (body:cm_stmt)) <=>
        cm_expr_scope_wf active guard &&
        cm_stmt_scope_wf active body) &&
     (cm_stmt_scope_wf active CMBreakS = T) &&
     (cm_stmt_scope_wf active CMContinueS = T) &&
     (!expr.
        cm_stmt_scope_wf active (CMReturnS (expr:cm_expr)) <=>
        cm_expr_scope_wf active expr)`);
PROOF int _e_cm_stmt_scope_wf =
    cst_add_const_to_header(`cm_stmt_scope_wf`);

PROOF thm cm_function_wf_def = new_fun_definition(
    `cm_function_wf (p:cm_program) (f:cm_function_d) : bool =
       (cm_scalar_type (cm_program_structs p) (cm_function_ret f) &&
        cm_params_wf (cm_program_structs p) (cm_function_params f) &&
        cm_slots_wf (cm_program_structs p) (cm_function_locals f) &&
        cm_stmt_wf p f F (cm_function_body f) &&
        cm_stmt_scope_wf (\i:int. F) (cm_function_body f) &&
        (!i. 0i <= i ==> i < ilength (cm_function_locals f) ==>
             cm_decl_count i (cm_function_body f) == 1i) &&
        0i <= cm_temp_slots f &&
        8i <= cm_frame_size (cm_program_structs p) f &&
        cm_frame_size (cm_program_structs p) f <= 1048560i)`);
PROOF int _e_cm_function_wf =
    cst_add_const_to_header(`cm_function_wf`);

PROOF thm cm_typed_program_def = new_fun_definition(
    `cm_typed_program (p:cm_program) : bool =
       ((!(i:int). 0i <= i ==> i < ilength (cm_program_structs p) ==>
           cm_struct_wf (cm_program_structs p)
             (inth i (cm_program_structs p))) &&
        (!(i:int). 0i <= i ==> i < ilength (cm_program_globals p) ==>
           cm_global_wf (cm_program_structs p)
             (inth i (cm_program_globals p))) &&
        (!(i:int). 0i <= i ==> i < ilength (cm_program_strings p) ==>
           cm_string_wf (inth i (cm_program_strings p))) &&
        (!(i:int). 0i <= i ==> i < ilength (cm_program_functions p) ==>
           cm_function_wf p (inth i (cm_program_functions p))) &&
        0i <= cm_program_main p &&
        cm_program_main p < ilength (cm_program_functions p) &&
        cm_function_ret
          (inth (cm_program_main p) (cm_program_functions p)) ==
          CMIntTy &&
        cm_function_params
          (inth (cm_program_main p) (cm_program_functions p)) == [] &&
        16i <= cm_static_size p &&
        cm_static_size p <= 1048576i)`);
PROOF int _e_cm_typed_program =
    cst_add_const_to_header(`cm_typed_program`);

PROOF thm get_cm_typed_program_def(void) {
  return cm_typed_program_def;
}
PROOF thm get_cm_type_refs_def(void) { return cm_type_refs_def; }
PROOF thm get_cm_struct_wf_def(void) { return cm_struct_wf_def; }
PROOF thm get_cm_expr_array_def(void) { return cm_expr_array_def; }
PROOF thm get_cm_expr_wf_def(void) { return cm_expr_wf_def; }
PROOF thm get_cm_args_wf_def(void) { return cm_expr_wf_def; }
PROOF thm get_cm_expr_type_def(void) { return cm_expr_type_def; }
PROOF thm get_cm_stmt_wf_def(void) { return cm_stmt_wf_def; }
PROOF thm get_cm_function_wf_def(void) { return cm_function_wf_def; }
PROOF thm get_cm_convertible_def(void) { return cm_convertible_def; }
PROOF thm get_cm_integer_type_def(void) { return cm_integer_type_def; }
PROOF thm get_cm_scalar_expr_type_def(void) {
  return cm_scalar_expr_type_def;
}
PROOF thm get_cm_zero_literal_def(void) { return cm_zero_literal_def; }
PROOF thm get_cm_expr_convertible_def(void) {
  return cm_expr_convertible_def;
}
PROOF thm get_cm_binding_valid_def(void) {
  return cm_binding_valid_def;
}
PROOF thm get_cm_member_valid_def(void) {
  return cm_member_valid_def;
}
PROOF thm get_cm_slot_wf_def(void) { return cm_slot_wf_def; }
PROOF thm get_cm_slots_wf_def(void) { return cm_slots_wf_def; }
PROOF thm get_cm_params_wf_def(void) { return cm_params_wf_def; }
PROOF thm get_cm_lvalue_def(void) { return cm_lvalue_def; }


/* --------------------------------------------------------------------- */
/* Source state: numeric bytes plus source-only initialization, pointer   */
/* provenance, live regions, environments, input/output, FP, freshness.   */
/* --------------------------------------------------------------------- */

PROOF indtype cm_region_ty = new_datatype_definition(
    "cm_region = CMRegion int int int int bool bool");
PROOF static int _t_cm_region = cst_add_type_to_header("cm_region", 0);
PROOF static int _c_CMRegion = cst_add_const_to_header(
    `CMRegion:int->int->int->int->bool->bool->cm_region`);

PROOF indtype cm_src_state_ty = new_datatype_definition(
    "cm_src_state = CMState (int->int) (int->bool) "
    "(int->cm_value) (int->bool) (int->int->cm_value) "
    "(int)list (int)list int int (cm_region)list");
PROOF static int _t_cm_src_state =
    cst_add_type_to_header("cm_src_state", 0);
PROOF static int _c_CMState = cst_add_const_to_header(
    `CMState:(int->int)->(int->bool)->(int->cm_value)->(int->bool)->
      (int->int->cm_value)->(int)list->(int)list->int->int->
      (cm_region)list->cm_src_state`);

PROOF indtype cm_control_ty = new_datatype_definition(
    "cm_control = CMNormal | CMBreak | CMContinue | "
    "CMReturn cm_value | CMExit int | CMError int");
PROOF static int _t_cm_control = cst_add_type_to_header("cm_control", 0);
PROOF static int _c_CMNormal =
    cst_add_const_to_header(`CMNormal:cm_control`);
PROOF static int _c_CMBreak =
    cst_add_const_to_header(`CMBreak:cm_control`);
PROOF static int _c_CMContinue =
    cst_add_const_to_header(`CMContinue:cm_control`);
PROOF static int _c_CMReturn =
    cst_add_const_to_header(`CMReturn:cm_value->cm_control`);
PROOF static int _c_CMExit =
    cst_add_const_to_header(`CMExit:int->cm_control`);
PROOF static int _c_CMError =
    cst_add_const_to_header(`CMError:int->cm_control`);

PROOF thm cm_region_gen_def = new_rec_definition(cm_region_ty.rec,
    `cm_region_gen
       (CMRegion (gen:int) (base:int) (lo:int) (hi:int)
          (writable:bool) (live:bool)) = gen`);
PROOF thm cm_region_base_field_def = new_rec_definition(cm_region_ty.rec,
    `cm_region_base_field
       (CMRegion (gen:int) (base:int) (lo:int) (hi:int)
          (writable:bool) (live:bool)) = base`);
PROOF thm cm_region_lo_def = new_rec_definition(cm_region_ty.rec,
    `cm_region_lo
       (CMRegion (gen:int) (base:int) (lo:int) (hi:int)
          (writable:bool) (live:bool)) = lo`);
PROOF thm cm_region_hi_def = new_rec_definition(cm_region_ty.rec,
    `cm_region_hi
       (CMRegion (gen:int) (base:int) (lo:int) (hi:int)
          (writable:bool) (live:bool)) = hi`);
PROOF thm cm_region_writable_def = new_rec_definition(cm_region_ty.rec,
    `cm_region_writable
       (CMRegion (gen:int) (base:int) (lo:int) (hi:int)
          (writable:bool) (live:bool)) = writable`);
PROOF thm cm_region_live_def = new_rec_definition(cm_region_ty.rec,
    `cm_region_live
       (CMRegion (gen:int) (base:int) (lo:int) (hi:int)
          (writable:bool) (live:bool)) = live`);
PROOF int _e_cm_region_gen = cst_add_const_to_header(`cm_region_gen`);
PROOF int _e_cm_region_base_field =
    cst_add_const_to_header(`cm_region_base_field`);
PROOF int _e_cm_region_lo = cst_add_const_to_header(`cm_region_lo`);
PROOF int _e_cm_region_hi = cst_add_const_to_header(`cm_region_hi`);
PROOF int _e_cm_region_writable =
    cst_add_const_to_header(`cm_region_writable`);
PROOF int _e_cm_region_live = cst_add_const_to_header(`cm_region_live`);
PROOF thm get_cm_region_gen_def(void) { return cm_region_gen_def; }
PROOF thm get_cm_region_base_field_def(void) {
  return cm_region_base_field_def;
}
PROOF thm get_cm_region_lo_def(void) { return cm_region_lo_def; }
PROOF thm get_cm_region_hi_def(void) { return cm_region_hi_def; }
PROOF thm get_cm_region_live_def(void) { return cm_region_live_def; }

PROOF thm cm_state_mem_def = new_rec_definition(cm_src_state_ty.rec,
    `cm_state_mem
       (CMState (mem:int->int) (init:int->bool)
          (tags:int->cm_value) (tagged:int->bool)
          (env:int->int->cm_value) (input:(int)list)
          (output:(int)list) (fp:int) (nextgen:int)
          (regions:(cm_region)list)) = mem`);
PROOF thm cm_state_init_def = new_rec_definition(cm_src_state_ty.rec,
    `cm_state_init
       (CMState (mem:int->int) (init:int->bool)
          (tags:int->cm_value) (tagged:int->bool)
          (env:int->int->cm_value) (input:(int)list)
          (output:(int)list) (fp:int) (nextgen:int)
          (regions:(cm_region)list)) = init`);
PROOF thm cm_state_tags_def = new_rec_definition(cm_src_state_ty.rec,
    `cm_state_tags
       (CMState (mem:int->int) (init:int->bool)
          (tags:int->cm_value) (tagged:int->bool)
          (env:int->int->cm_value) (input:(int)list)
          (output:(int)list) (fp:int) (nextgen:int)
          (regions:(cm_region)list)) = tags`);
PROOF thm cm_state_tagged_def = new_rec_definition(cm_src_state_ty.rec,
    `cm_state_tagged
       (CMState (mem:int->int) (init:int->bool)
          (tags:int->cm_value) (tagged:int->bool)
          (env:int->int->cm_value) (input:(int)list)
          (output:(int)list) (fp:int) (nextgen:int)
          (regions:(cm_region)list)) = tagged`);
PROOF thm cm_state_env_def = new_rec_definition(cm_src_state_ty.rec,
    `cm_state_env
       (CMState (mem:int->int) (init:int->bool)
          (tags:int->cm_value) (tagged:int->bool)
          (env:int->int->cm_value) (input:(int)list)
          (output:(int)list) (fp:int) (nextgen:int)
          (regions:(cm_region)list)) = env`);
PROOF thm cm_state_input_def = new_rec_definition(cm_src_state_ty.rec,
    `cm_state_input
       (CMState (mem:int->int) (init:int->bool)
          (tags:int->cm_value) (tagged:int->bool)
          (env:int->int->cm_value) (input:(int)list)
          (output:(int)list) (fp:int) (nextgen:int)
          (regions:(cm_region)list)) = input`);
PROOF thm cm_state_output_def = new_rec_definition(cm_src_state_ty.rec,
    `cm_state_output
       (CMState (mem:int->int) (init:int->bool)
          (tags:int->cm_value) (tagged:int->bool)
          (env:int->int->cm_value) (input:(int)list)
          (output:(int)list) (fp:int) (nextgen:int)
          (regions:(cm_region)list)) = output`);
PROOF thm cm_state_fp_def = new_rec_definition(cm_src_state_ty.rec,
    `cm_state_fp
       (CMState (mem:int->int) (init:int->bool)
          (tags:int->cm_value) (tagged:int->bool)
          (env:int->int->cm_value) (input:(int)list)
          (output:(int)list) (fp:int) (nextgen:int)
          (regions:(cm_region)list)) = fp`);
PROOF thm cm_state_nextgen_def = new_rec_definition(cm_src_state_ty.rec,
    `cm_state_nextgen
       (CMState (mem:int->int) (init:int->bool)
          (tags:int->cm_value) (tagged:int->bool)
          (env:int->int->cm_value) (input:(int)list)
          (output:(int)list) (fp:int) (nextgen:int)
          (regions:(cm_region)list)) = nextgen`);
PROOF thm cm_state_regions_def = new_rec_definition(cm_src_state_ty.rec,
    `cm_state_regions
       (CMState (mem:int->int) (init:int->bool)
          (tags:int->cm_value) (tagged:int->bool)
          (env:int->int->cm_value) (input:(int)list)
          (output:(int)list) (fp:int) (nextgen:int)
          (regions:(cm_region)list)) = regions`);
PROOF int _e_cm_state_mem = cst_add_const_to_header(`cm_state_mem`);
PROOF int _e_cm_state_init = cst_add_const_to_header(`cm_state_init`);
PROOF int _e_cm_state_tags = cst_add_const_to_header(`cm_state_tags`);
PROOF int _e_cm_state_tagged = cst_add_const_to_header(`cm_state_tagged`);
PROOF int _e_cm_state_env = cst_add_const_to_header(`cm_state_env`);
PROOF int _e_cm_state_input = cst_add_const_to_header(`cm_state_input`);
PROOF int _e_cm_state_output = cst_add_const_to_header(`cm_state_output`);
PROOF int _e_cm_state_fp = cst_add_const_to_header(`cm_state_fp`);
PROOF int _e_cm_state_nextgen =
    cst_add_const_to_header(`cm_state_nextgen`);
PROOF int _e_cm_state_regions =
    cst_add_const_to_header(`cm_state_regions`);

PROOF thm cm_state_make_def = new_fun_definition(
    `cm_state_make (mem:int->int) (init:int->bool)
       (tags:int->cm_value) (tagged:int->bool)
       (env:int->int->cm_value) (input:(int)list)
       (output:(int)list) (fp:int) (nextgen:int)
       (regions:(cm_region)list) : cm_src_state =
       CMState mem init tags tagged env input output fp nextgen regions`);
PROOF int _e_cm_state_make = cst_add_const_to_header(`cm_state_make`);

PROOF thm cm_region_base_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_region_base ([]:(cm_region)list) (gen:int) = gen) &&
     (!r rest gen.
        cm_region_base
          ((r:cm_region) :: (rest:(cm_region)list)) (gen:int) =
        (if cm_region_gen r == gen
         then cm_region_base_field r
         else cm_region_base rest gen))`);
PROOF int _e_cm_region_base = cst_add_const_to_header(`cm_region_base`);

PROOF thm cm_value_type_def = new_rec_definition(cm_value_RECURSION,
    `(!n. cm_value_type (CMIntV (n:int)) = CMIntTy) &&
     (!n. cm_value_type (CMCharV (n:int)) = CMCharTy) &&
     (cm_value_type CMNullV = CMPtrTy CMCharTy) &&
     (!gen lo hi off ty.
        cm_value_type
          (CMPtrV (gen:int) (lo:int) (hi:int) (off:int)
             (ty:cm_type)) = CMPtrTy ty)`);
PROOF int _e_cm_value_type = cst_add_const_to_header(`cm_value_type`);

PROOF thm cm_value_number_def = new_rec_definition(cm_value_RECURSION,
    `(!n st. cm_value_number (st:cm_src_state) (CMIntV (n:int)) =
        tower_wrap64 n) &&
     (!n st. cm_value_number st (CMCharV (n:int)) = tower_u8 n) &&
     (!st. cm_value_number (st:cm_src_state) CMNullV = 0i) &&
     (!gen lo hi off ty st.
        cm_value_number (st:cm_src_state)
          (CMPtrV (gen:int) (lo:int) (hi:int) (off:int)
             (ty:cm_type)) =
        tower_wrap64
          (cm_region_base (cm_state_regions st) gen + off))`);
PROOF int _e_cm_value_number = cst_add_const_to_header(`cm_value_number`);

PROOF thm cm_pointer_retype_def = new_rec_definition(cm_value_RECURSION,
    `(!n ty. cm_pointer_retype (ty:cm_type) (CMIntV (n:int)) =
        (if tower_wrap64 n == 0i then CMNullV else CMIntV n)) &&
     (!n ty. cm_pointer_retype (ty:cm_type) (CMCharV (n:int)) =
        (if tower_u8 n == 0i then CMNullV else CMCharV n)) &&
     (!ty. cm_pointer_retype (ty:cm_type) CMNullV = CMNullV) &&
     (!gen lo hi off oldty ty.
        cm_pointer_retype (ty:cm_type)
          (CMPtrV (gen:int) (lo:int) (hi:int) (off:int)
             (oldty:cm_type)) =
        CMPtrV gen lo hi off (cm_pointee ty))`);
PROOF int _e_cm_pointer_retype =
    cst_add_const_to_header(`cm_pointer_retype`);

PROOF thm cm_convert_value_def = new_fun_definition(
    `cm_convert_value (st:cm_src_state) (ty:cm_type)
       (v:cm_value) : cm_value =
       (if ty == CMIntTy
        then CMIntV (tower_wrap64 (cm_value_number st v))
        else if ty == CMCharTy
             then CMCharV (tower_u8 (cm_value_number st v))
             else cm_pointer_retype ty v)`);
PROOF int _e_cm_convert_value =
    cst_add_const_to_header(`cm_convert_value`);

PROOF thm cm_truth_def = new_fun_definition(
    `cm_truth (st:cm_src_state) (v:cm_value) : bool =
       ~(cm_value_number st v == 0i)`);
PROOF int _e_cm_truth = cst_add_const_to_header(`cm_truth`);

PROOF thm cm_ptr_offset_def = new_rec_definition(cm_value_RECURSION,
    `(!n. cm_ptr_offset (CMIntV (n:int)) = 0i) &&
     (!n. cm_ptr_offset (CMCharV (n:int)) = 0i) &&
     (cm_ptr_offset CMNullV = 0i) &&
     (!gen lo hi off ty.
        cm_ptr_offset
          (CMPtrV (gen:int) (lo:int) (hi:int) (off:int)
             (ty:cm_type)) = off)`);
PROOF thm cm_ptr_gen_def = new_rec_definition(cm_value_RECURSION,
    `(!n. cm_ptr_gen (CMIntV (n:int)) = --1i) &&
     (!n. cm_ptr_gen (CMCharV (n:int)) = --1i) &&
     (cm_ptr_gen CMNullV = --1i) &&
     (!gen lo hi off ty.
        cm_ptr_gen
          (CMPtrV (gen:int) (lo:int) (hi:int) (off:int)
             (ty:cm_type)) = gen)`);
PROOF thm cm_ptr_lo_def = new_rec_definition(cm_value_RECURSION,
    `(!n. cm_ptr_lo (CMIntV (n:int)) = 0i) &&
     (!n. cm_ptr_lo (CMCharV (n:int)) = 0i) &&
     (cm_ptr_lo CMNullV = 0i) &&
     (!gen lo hi off ty.
        cm_ptr_lo
          (CMPtrV (gen:int) (lo:int) (hi:int) (off:int)
             (ty:cm_type)) = lo)`);
PROOF thm cm_ptr_hi_def = new_rec_definition(cm_value_RECURSION,
    `(!n. cm_ptr_hi (CMIntV (n:int)) = 0i) &&
     (!n. cm_ptr_hi (CMCharV (n:int)) = 0i) &&
     (cm_ptr_hi CMNullV = 0i) &&
     (!gen lo hi off ty.
        cm_ptr_hi
          (CMPtrV (gen:int) (lo:int) (hi:int) (off:int)
             (ty:cm_type)) = hi)`);
PROOF thm cm_ptr_view_def = new_rec_definition(cm_value_RECURSION,
    `(!n. cm_ptr_view (CMIntV (n:int)) = CMIntTy) &&
     (!n. cm_ptr_view (CMCharV (n:int)) = CMCharTy) &&
     (cm_ptr_view CMNullV = CMCharTy) &&
     (!gen lo hi off ty.
        cm_ptr_view
          (CMPtrV (gen:int) (lo:int) (hi:int) (off:int)
             (ty:cm_type)) = ty)`);
PROOF int _e_cm_ptr_offset = cst_add_const_to_header(`cm_ptr_offset`);
PROOF int _e_cm_ptr_gen = cst_add_const_to_header(`cm_ptr_gen`);
PROOF int _e_cm_ptr_lo = cst_add_const_to_header(`cm_ptr_lo`);
PROOF int _e_cm_ptr_hi = cst_add_const_to_header(`cm_ptr_hi`);
PROOF int _e_cm_ptr_view = cst_add_const_to_header(`cm_ptr_view`);

PROOF thm cm_ptr_add_def = new_fun_definition(
    `cm_ptr_add (structs:(cm_struct_d)list) (p:cm_value)
       (index:int) : cm_value =
       CMPtrV (cm_ptr_gen p) (cm_ptr_lo p) (cm_ptr_hi p)
         (cm_ptr_offset p +
          index * cm_type_size structs (cm_ptr_view p))
         (cm_ptr_view p)`);
PROOF int _e_cm_ptr_add = cst_add_const_to_header(`cm_ptr_add`);

PROOF thm cm_is_null_value_def = new_rec_definition(cm_value_RECURSION,
    `(!n. cm_is_null_value (CMIntV (n:int)) = F) &&
     (!n. cm_is_null_value (CMCharV (n:int)) = F) &&
     (cm_is_null_value CMNullV = T) &&
     (!gen lo hi off ty.
        cm_is_null_value
          (CMPtrV (gen:int) (lo:int) (hi:int) (off:int)
            (ty:cm_type)) = F)`);
PROOF int _e_cm_is_null_value =
    cst_add_const_to_header(`cm_is_null_value`);

PROOF thm cm_pointer_region_ok_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_pointer_region_ok ([]:(cm_region)list) (ptr:cm_value)
        (write:bool) = F) &&
     (!r rest.
        cm_pointer_region_ok
          ((r:cm_region) :: (rest:(cm_region)list))
          (ptr:cm_value) (write:bool) =
        ((cm_region_gen r == cm_ptr_gen ptr &&
          cm_region_live r &&
          cm_region_lo r <= cm_ptr_lo ptr &&
          cm_ptr_hi ptr <= cm_region_hi r &&
          (~write || cm_region_writable r)) ||
         cm_pointer_region_ok rest ptr write))`);
PROOF thm cm_pointer_live_def = new_fun_definition(
    `cm_pointer_live (st:cm_src_state) (ptr:cm_value) : bool =
       (0i <= cm_ptr_gen ptr &&
        cm_ptr_lo ptr <= cm_ptr_hi ptr &&
        cm_pointer_region_ok (cm_state_regions st) ptr F)`);
PROOF thm cm_pointer_writable_def = new_fun_definition(
    `cm_pointer_writable (st:cm_src_state) (ptr:cm_value) : bool =
       (cm_pointer_live st ptr &&
        cm_pointer_region_ok (cm_state_regions st) ptr T)`);
PROOF int _e_cm_pointer_region_ok =
    cst_add_const_to_header(`cm_pointer_region_ok`);
PROOF int _e_cm_pointer_live =
    cst_add_const_to_header(`cm_pointer_live`);
PROOF int _e_cm_pointer_writable =
    cst_add_const_to_header(`cm_pointer_writable`);

PROOF thm cm_pointer_compatible_def = new_fun_definition(
    `cm_pointer_compatible (st:cm_src_state)
       (left:cm_value) (right:cm_value) : bool =
       (~(cm_is_null_value left) && ~(cm_is_null_value right) &&
        cm_pointer_live st left && cm_pointer_live st right &&
        cm_ptr_gen left == cm_ptr_gen right &&
        cm_ptr_lo left == cm_ptr_lo right &&
        cm_ptr_hi left == cm_ptr_hi right &&
        cm_ptr_view left == cm_ptr_view right)`);
PROOF thm cm_pointer_equality_ok_def = new_fun_definition(
    `cm_pointer_equality_ok (st:cm_src_state)
       (left:cm_value) (right:cm_value) : bool =
       ((cm_is_null_value left && cm_is_null_value right) ||
        (cm_is_null_value left && cm_pointer_live st right) ||
        (cm_pointer_live st left && cm_is_null_value right) ||
        cm_pointer_compatible st left right)`);
PROOF int _e_cm_pointer_compatible =
    cst_add_const_to_header(`cm_pointer_compatible`);
PROOF int _e_cm_pointer_equality_ok =
    cst_add_const_to_header(`cm_pointer_equality_ok`);

PROOF thm cm_ptr_shift_ok_def = new_fun_definition(
    `cm_ptr_shift_ok (structs:(cm_struct_d)list)
       (ptr:cm_value) (index:int) (st:cm_src_state) : bool =
       (cm_pointer_live st ptr &&
        0i < cm_type_size structs (cm_ptr_view ptr) &&
        cm_ptr_lo ptr <=
          cm_ptr_offset ptr +
            index * cm_type_size structs (cm_ptr_view ptr) &&
        cm_ptr_offset ptr +
          index * cm_type_size structs (cm_ptr_view ptr) <=
          cm_ptr_hi ptr)`);
PROOF thm cm_ptr_diff_ok_def = new_fun_definition(
    `cm_ptr_diff_ok (structs:(cm_struct_d)list)
       (left:cm_value) (right:cm_value)
       (st:cm_src_state) : bool =
       (cm_pointer_compatible st left right &&
        0i < cm_type_size structs (cm_ptr_view left) &&
        (cm_ptr_offset left - cm_ptr_offset right) %
          cm_type_size structs (cm_ptr_view left) == 0i)`);
PROOF int _e_cm_ptr_shift_ok =
    cst_add_const_to_header(`cm_ptr_shift_ok`);
PROOF int _e_cm_ptr_diff_ok =
    cst_add_const_to_header(`cm_ptr_diff_ok`);

PROOF thm cm_binary_ok_def = new_fun_definition(
    `cm_binary_ok (p:cm_program) (op:int)
       (left:cm_value) (right:cm_value)
       (st:cm_src_state) : bool =
       (if op == 2i || op == 3i
        then if cm_is_pointer (cm_value_type left) ||
                cm_is_pointer (cm_value_type right)
             then cm_pointer_equality_ok st left right
             else T
        else if 4i <= op && op <= 7i
             then if cm_is_pointer (cm_value_type left) ||
                     cm_is_pointer (cm_value_type right)
                  then cm_pointer_compatible st left right
                  else T
        else if op == 8i
             then if cm_is_pointer (cm_value_type left)
                  then cm_ptr_shift_ok (cm_program_structs p) left
                         (cm_value_number st right) st
                  else if cm_is_pointer (cm_value_type right)
                       then cm_ptr_shift_ok (cm_program_structs p) right
                              (cm_value_number st left) st
                       else T
        else if op == 9i
             then if cm_is_pointer (cm_value_type left) &&
                     cm_is_pointer (cm_value_type right)
                  then cm_ptr_diff_ok (cm_program_structs p) left right st
                  else if cm_is_pointer (cm_value_type left)
                       then cm_ptr_shift_ok (cm_program_structs p) left
                              (tower_neg (cm_value_number st right)) st
                       else T
        else if op == 11i || op == 12i
             then ~(cm_value_number st right == 0i)
             else T)`);
PROOF int _e_cm_binary_ok =
    cst_add_const_to_header(`cm_binary_ok`);

PROOF thm cm_state_io_def = new_fun_definition(
    `cm_state_io (st:cm_src_state) (input:(int)list)
       (output:(int)list) : cm_src_state =
       cm_state_make (cm_state_mem st) (cm_state_init st)
         (cm_state_tags st) (cm_state_tagged st)
         (cm_state_env st) input output (cm_state_fp st)
         (cm_state_nextgen st) (cm_state_regions st)`);
PROOF thm cm_state_env_set_def = new_fun_definition(
    `cm_state_env_set (st:cm_src_state)
       (env:int->int->cm_value) : cm_src_state =
       cm_state_make (cm_state_mem st) (cm_state_init st)
         (cm_state_tags st) (cm_state_tagged st) env
         (cm_state_input st) (cm_state_output st) (cm_state_fp st)
         (cm_state_nextgen st) (cm_state_regions st)`);
PROOF thm cm_state_frame_def = new_fun_definition(
    `cm_state_frame (st:cm_src_state) (env:int->int->cm_value)
       (fp:int) (nextgen:int) (regions:(cm_region)list) :
       cm_src_state =
       cm_state_make (cm_state_mem st) (cm_state_init st)
         (cm_state_tags st) (cm_state_tagged st) env
         (cm_state_input st) (cm_state_output st) fp nextgen regions`);
PROOF int _e_cm_state_io = cst_add_const_to_header(`cm_state_io`);
PROOF int _e_cm_state_env_set =
    cst_add_const_to_header(`cm_state_env_set`);
PROOF int _e_cm_state_frame = cst_add_const_to_header(`cm_state_frame`);

PROOF thm cm_store_width_def = new_fun_definition(
    `cm_store_width (ty:cm_type) : int =
       (if ty == CMCharTy then 1i else 8i)`);
PROOF int _e_cm_store_width = cst_add_const_to_header(`cm_store_width`);

PROOF thm cm_mark_init_def = new_fun_definition(
    `cm_mark_init (old:int->bool) (base:int) (width:int) : int->bool =
       (\a:int. old a || (base <= a && a < base + width))`);
PROOF int _e_cm_mark_init = cst_add_const_to_header(`cm_mark_init`);

PROOF thm cm_clear_init_def = new_fun_definition(
    `cm_clear_init (old:int->bool) (base:int) (width:int) : int->bool =
       (\a:int. old a && ~(base <= a && a < base + width))`);
PROOF int _e_cm_clear_init =
    cst_add_const_to_header(`cm_clear_init`);

PROOF thm cm_clear_tagged_def = new_fun_definition(
    `cm_clear_tagged (old:int->bool) (base:int) (width:int) :
       int->bool =
       (\a:int.
          old a &&
          ~(0i < width && a < base + width && base < a + 8i))`);
PROOF int _e_cm_clear_tagged =
    cst_add_const_to_header(`cm_clear_tagged`);

PROOF thm cm_store_mem_def = new_fun_definition(
    `cm_store_mem (ty:cm_type) (base:int) (n:int)
       (mem:int->int) : int->int =
       (if ty == CMCharTy
        then tower_setb mem base (tower_u8 n)
        else tower_setw mem base (tower_wrap64 n))`);
PROOF int _e_cm_store_mem = cst_add_const_to_header(`cm_store_mem`);

PROOF thm cm_state_store_def = new_fun_definition(
    `cm_state_store (ty:cm_type) (ptr:cm_value) (v:cm_value)
       (st:cm_src_state) : cm_src_state =
       cm_state_make
         (cm_store_mem ty (cm_value_number st ptr)
            (cm_value_number st (cm_convert_value st ty v))
            (cm_state_mem st))
         (cm_mark_init (cm_state_init st) (cm_value_number st ptr)
            (cm_store_width ty))
         (if cm_is_pointer ty
          then (\a:int.
             if a == cm_value_number st ptr
             then cm_convert_value st ty v
             else cm_state_tags st a)
          else cm_state_tags st)
         (if cm_is_pointer ty
          then (\a:int.
             (a == cm_value_number st ptr &&
              ~(cm_value_number st (cm_convert_value st ty v) == 0i)) ||
             cm_clear_tagged (cm_state_tagged st)
               (cm_value_number st ptr) 8i a)
          else cm_clear_tagged (cm_state_tagged st)
                 (cm_value_number st ptr) (cm_store_width ty))
         (cm_state_env st) (cm_state_input st) (cm_state_output st)
         (cm_state_fp st) (cm_state_nextgen st) (cm_state_regions st)`);
PROOF int _e_cm_state_store = cst_add_const_to_header(`cm_state_store`);

PROOF thm cm_bytes_initialized_def = new_fun_definition(
    `cm_bytes_initialized (init:int->bool) (base:int)
       (width:int) : bool =
       (init base &&
        (width == 1i ||
         (init (base + 1i) && init (base + 2i) &&
          init (base + 3i) && init (base + 4i) &&
          init (base + 5i) && init (base + 6i) &&
          init (base + 7i))))`);
PROOF int _e_cm_bytes_initialized =
    cst_add_const_to_header(`cm_bytes_initialized`);

PROOF thm cm_store_ok_def = new_fun_definition(
    `cm_store_ok (ty:cm_type) (ptr:cm_value)
       (st:cm_src_state) : bool =
       (cm_pointer_writable st ptr &&
        cm_ptr_lo ptr <= cm_ptr_offset ptr &&
        cm_ptr_offset ptr + cm_store_width ty <= cm_ptr_hi ptr &&
        (if ty == CMCharTy
         then tower_addr_valid (cm_value_number st ptr)
         else tower_word_valid (cm_value_number st ptr)))`);
PROOF int _e_cm_store_ok = cst_add_const_to_header(`cm_store_ok`);

PROOF thm cm_load_ok_def = new_fun_definition(
    `cm_load_ok (ty:cm_type) (ptr:cm_value)
       (st:cm_src_state) : bool =
       (cm_pointer_live st ptr &&
        cm_ptr_lo ptr <= cm_ptr_offset ptr &&
        cm_ptr_offset ptr + cm_store_width ty <= cm_ptr_hi ptr &&
        (if ty == CMCharTy
         then tower_addr_valid (cm_value_number st ptr)
         else tower_word_valid (cm_value_number st ptr)) &&
        cm_bytes_initialized (cm_state_init st)
          (cm_value_number st ptr) (cm_store_width ty) &&
        (cm_is_pointer ty ==>
          (tower_getw (cm_state_mem st)
             (cm_value_number st ptr) == 0i ||
           (cm_state_tagged st (cm_value_number st ptr) &&
            cm_is_pointer
              (cm_value_type
                (cm_state_tags st (cm_value_number st ptr)))))))`);
PROOF int _e_cm_load_ok = cst_add_const_to_header(`cm_load_ok`);

PROOF thm cm_load_value_def = new_fun_definition(
    `cm_load_value (ty:cm_type) (ptr:cm_value)
       (st:cm_src_state) : cm_value =
       (if ty == CMCharTy
        then CMCharV
          (tower_getb (cm_state_mem st)
            (cm_value_number st ptr))
        else if ty == CMIntTy
             then CMIntV
               (tower_getw (cm_state_mem st)
                 (cm_value_number st ptr))
             else if tower_getw (cm_state_mem st)
                       (cm_value_number st ptr) == 0i
                  then CMNullV
                  else cm_pointer_retype ty
                    (cm_state_tags st (cm_value_number st ptr)))`);
PROOF int _e_cm_load_value = cst_add_const_to_header(`cm_load_value`);

PROOF thm cm_binary_value_def = new_fun_definition(
    `cm_binary_value (p:cm_program) (op:int) (left:cm_value)
       (right:cm_value) (ty:cm_type) (st:cm_src_state) : cm_value =
       (if op == 0i
        then CMIntV (tower_bool (cm_truth st left || cm_truth st right))
        else if op == 1i
             then CMIntV
               (tower_bool (cm_truth st left && cm_truth st right))
        else if op == 2i
             then CMIntV (tower_bool
               (cm_value_number st left == cm_value_number st right))
        else if op == 3i
             then CMIntV (tower_bool
               (~(cm_value_number st left == cm_value_number st right)))
        else if op == 4i
             then CMIntV (tower_bool
               (cm_value_number st left < cm_value_number st right))
        else if op == 5i
             then CMIntV (tower_bool
               (cm_value_number st left <= cm_value_number st right))
        else if op == 6i
             then CMIntV (tower_bool
               (cm_value_number st left > cm_value_number st right))
        else if op == 7i
             then CMIntV (tower_bool
               (cm_value_number st left >= cm_value_number st right))
        else if op == 8i && cm_is_pointer (cm_value_type left)
             then cm_ptr_add (cm_program_structs p) left
               (cm_value_number st right)
        else if op == 8i && cm_is_pointer (cm_value_type right)
             then cm_ptr_add (cm_program_structs p) right
               (cm_value_number st left)
        else if op == 8i
             then CMIntV (tower_add
               (cm_value_number st left) (cm_value_number st right))
        else if op == 9i && cm_is_pointer (cm_value_type left) &&
                cm_is_pointer (cm_value_type right)
             then CMIntV (tower_div
               (tower_sub (cm_ptr_offset left) (cm_ptr_offset right))
               (cm_type_size (cm_program_structs p)
                 (cm_ptr_view left)))
        else if op == 9i && cm_is_pointer (cm_value_type left)
             then cm_ptr_add (cm_program_structs p) left
               (tower_neg (cm_value_number st right))
        else if op == 9i
             then CMIntV (tower_sub
               (cm_value_number st left) (cm_value_number st right))
        else if op == 10i
             then CMIntV (tower_mul
               (cm_value_number st left) (cm_value_number st right))
        else if op == 11i
             then CMIntV (tower_div
               (cm_value_number st left) (cm_value_number st right))
        else CMIntV (tower_mod
               (cm_value_number st left) (cm_value_number st right)))`);
PROOF int _e_cm_binary_value =
    cst_add_const_to_header(`cm_binary_value`);

PROOF thm cm_unary_value_def = new_fun_definition(
    `cm_unary_value (op:int) (arg:cm_value)
       (st:cm_src_state) : cm_value =
       (if op == 0i
        then CMIntV (tower_neg (cm_value_number st arg))
        else CMIntV (tower_bool (~(cm_truth st arg))))`);
PROOF int _e_cm_unary_value = cst_add_const_to_header(`cm_unary_value`);

PROOF thm cm_slots_prefix_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_slots_prefix (structs:(cm_struct_d)list)
        ([]:(cm_slot_d)list) (index:int) = 0i) &&
     (!slot rest index.
        cm_slots_prefix structs
          ((slot:cm_slot_d) :: (rest:(cm_slot_d)list)) (index:int) =
        (if index == 0i then 0i
         else cm_slot_size structs slot +
              cm_slots_prefix structs rest (index - 1i)))`);
PROOF int _e_cm_slots_prefix = cst_add_const_to_header(`cm_slots_prefix`);

PROOF thm cm_globals_prefix_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_globals_prefix (structs:(cm_struct_d)list)
        ([]:(cm_global_d)list) (index:int) = 0i) &&
     (!g rest index.
        cm_globals_prefix structs
          ((g:cm_global_d) :: (rest:(cm_global_d)list)) (index:int) =
        (if index == 0i then 0i
         else cm_global_size structs g +
              cm_globals_prefix structs rest (index - 1i)))`);
PROOF int _e_cm_globals_prefix =
    cst_add_const_to_header(`cm_globals_prefix`);

PROOF thm cm_strings_prefix_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_strings_prefix ([]:(cm_string_d)list) (index:int) = 0i) &&
     (!s rest index.
        cm_strings_prefix
          ((s:cm_string_d) :: (rest:(cm_string_d)list)) (index:int) =
        (if index == 0i then 0i
         else ilength (cm_string_bytes s) + 1i +
              cm_strings_prefix rest (index - 1i)))`);
PROOF int _e_cm_strings_prefix =
    cst_add_const_to_header(`cm_strings_prefix`);

PROOF thm cm_global_address_def = new_fun_definition(
    `cm_global_address (p:cm_program) (index:int) : int =
       16i + cm_globals_prefix (cm_program_structs p)
         (cm_program_globals p) index`);
PROOF thm cm_string_address_def = new_fun_definition(
    `cm_string_address (p:cm_program) (index:int) : int =
       16i +
       cm_globals_size (cm_program_structs p) (cm_program_globals p) +
       cm_strings_prefix (cm_program_strings p) index`);
PROOF int _e_cm_global_address =
    cst_add_const_to_header(`cm_global_address`);
PROOF int _e_cm_string_address =
    cst_add_const_to_header(`cm_string_address`);
PROOF thm get_cm_slots_prefix_def(void) { return cm_slots_prefix_def; }
PROOF thm get_cm_globals_prefix_def(void) { return cm_globals_prefix_def; }
PROOF thm get_cm_strings_prefix_def(void) { return cm_strings_prefix_def; }
PROOF thm get_cm_global_address_def(void) { return cm_global_address_def; }
PROOF thm get_cm_string_address_def(void) { return cm_string_address_def; }

PROOF thm cm_global_generation_def = new_fun_definition(
    `cm_global_generation (index:int) : int = 1i + index`);
PROOF thm cm_string_generation_def = new_fun_definition(
    `cm_string_generation (p:cm_program) (index:int) : int =
       1i + ilength (cm_program_globals p) + index`);
PROOF thm cm_first_dynamic_generation_def = new_fun_definition(
    `cm_first_dynamic_generation (p:cm_program) : int =
       1i + ilength (cm_program_globals p) +
       ilength (cm_program_strings p)`);
PROOF int _e_cm_global_generation =
    cst_add_const_to_header(`cm_global_generation`);
PROOF int _e_cm_string_generation =
    cst_add_const_to_header(`cm_string_generation`);
PROOF int _e_cm_first_dynamic_generation =
    cst_add_const_to_header(`cm_first_dynamic_generation`);

PROOF thm cm_global_pointer_def = new_fun_definition(
    `cm_global_pointer (p:cm_program) (index:int) : cm_value =
       CMPtrV (cm_global_generation index) 0i
         (cm_global_size (cm_program_structs p)
           (inth index (cm_program_globals p)))
         0i
         (cm_global_ty (inth index (cm_program_globals p)))`);
PROOF thm cm_string_pointer_def = new_fun_definition(
    `cm_string_pointer (p:cm_program) (index:int) : cm_value =
       CMPtrV (cm_string_generation p index) 0i
         (ilength (cm_string_bytes
           (inth index (cm_program_strings p))) + 1i)
         0i CMCharTy`);
PROOF int _e_cm_global_pointer =
    cst_add_const_to_header(`cm_global_pointer`);
PROOF int _e_cm_string_pointer =
    cst_add_const_to_header(`cm_string_pointer`);

PROOF thm cm_global_regions_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_global_regions (p:cm_program) ([]:(cm_global_d)list)
        (index:int) = ([]:(cm_region)list)) &&
     (!g rest.
        cm_global_regions p
          ((g:cm_global_d) :: (rest:(cm_global_d)list)) (index:int) =
        CMRegion (cm_global_generation index)
          (cm_global_address p index) 0i
          (cm_global_size (cm_program_structs p) g) T T ::
        cm_global_regions p rest (index + 1i))`);
PROOF thm cm_string_regions_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_string_regions (p:cm_program) ([]:(cm_string_d)list)
        (index:int) = ([]:(cm_region)list)) &&
     (!s rest.
        cm_string_regions p
          ((s:cm_string_d) :: (rest:(cm_string_d)list)) (index:int) =
        CMRegion (cm_string_generation p index)
          (cm_string_address p index) 0i
          (ilength (cm_string_bytes s) + 1i) F T ::
        cm_string_regions p rest (index + 1i))`);
PROOF int _e_cm_global_regions =
    cst_add_const_to_header(`cm_global_regions`);
PROOF int _e_cm_string_regions =
    cst_add_const_to_header(`cm_string_regions`);

PROOF thm cm_write_bytes_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_write_bytes (mem:int->int) (base:int) ([]:(int)list) =
        mem) &&
     (!byte rest.
        cm_write_bytes mem base
          ((byte:int) :: (rest:(int)list)) =
        cm_write_bytes (tower_setb mem base byte)
          (base + 1i) rest)`);
PROOF int _e_cm_write_bytes = cst_add_const_to_header(`cm_write_bytes`);

PROOF thm cm_static_global_init_bytes_def = new_fun_definition(
    `cm_static_global_init_bytes (g:cm_global_d) : (int)list =
       (if cm_global_ty g == CMCharTy
        then [tower_u8 (cm_global_init g)]
        else tower_word_bytes (cm_global_init g))`);
PROOF int _e_cm_static_global_init_bytes =
    cst_add_const_to_header(`cm_static_global_init_bytes`);

PROOF thm cm_static_global_bytes_def = new_fun_definition(
    `cm_static_global_bytes (structs:(cm_struct_d)list)
       (g:cm_global_d) : (int)list =
       (let size = cm_global_size structs g in
        let initial = cm_static_global_init_bytes g in
        if 0i <= size
        then if cm_global_has_init g && ilength initial <= size
             then initial ++ ireplicate (size - ilength initial) 0i
             else ireplicate size 0i
        else [])`);
PROOF int _e_cm_static_global_bytes =
    cst_add_const_to_header(`cm_static_global_bytes`);

PROOF thm cm_static_globals_bytes_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!structs.
       cm_static_globals_bytes (structs:(cm_struct_d)list)
         ([]:(cm_global_d)list) = []) &&
     (!structs g rest.
       cm_static_globals_bytes (structs:(cm_struct_d)list)
         ((g:cm_global_d) :: (rest:(cm_global_d)list)) =
       cm_static_global_bytes structs g ++
         cm_static_globals_bytes structs rest)`);
PROOF int _e_cm_static_globals_bytes =
    cst_add_const_to_header(`cm_static_globals_bytes`);

PROOF thm cm_static_strings_bytes_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_static_strings_bytes ([]:(cm_string_d)list) = []) &&
     (!s rest.
       cm_static_strings_bytes
         ((s:cm_string_d) :: (rest:(cm_string_d)list)) =
       cm_string_bytes s ++ [0i] ++
         cm_static_strings_bytes rest)`);
PROOF int _e_cm_static_strings_bytes =
    cst_add_const_to_header(`cm_static_strings_bytes`);

PROOF thm cm_static_data_bytes_def = new_fun_definition(
    `cm_static_data_bytes (p:cm_program) : (int)list =
       ireplicate 8i 0i ++
       cm_static_globals_bytes (cm_program_structs p)
         (cm_program_globals p) ++
       cm_static_strings_bytes (cm_program_strings p)`);
PROOF int _e_cm_static_data_bytes =
    cst_add_const_to_header(`cm_static_data_bytes`);

PROOF thm cm_initial_mem_def = new_fun_definition(
    `cm_initial_mem (p:cm_program) : int->int =
       cm_write_bytes tower_zero_mem 8i (cm_static_data_bytes p)`);
PROOF int _e_cm_initial_mem = cst_add_const_to_header(`cm_initial_mem`);

PROOF thm cm_initial_state_def = new_fun_definition(
    `cm_initial_state (p:cm_program) (input:(int)list) : cm_src_state =
       cm_state_make (cm_initial_mem p)
         (\a:int. 16i <= a && a < cm_static_size p)
         (\a:int. CMNullV) (\a:int. F)
         (\scope:int slot:int.
            if scope == 0i then cm_global_pointer p slot else CMNullV)
         input [] 1048576i (cm_first_dynamic_generation p)
         (APPEND
           (cm_global_regions p (cm_program_globals p) 0i)
           (cm_string_regions p (cm_program_strings p) 0i))`);
PROOF int _e_cm_initial_state = cst_add_const_to_header(`cm_initial_state`);
PROOF thm get_cm_initial_state_def(void) {
  return cm_initial_state_def;
}

/* Continuation frames make the source machine a deterministic small-step */
/* function while preserving the specified left-to-right evaluation order. */
PROOF indtype cm_frame_ty = new_datatype_definition(
    "cm_frame = CMHaltK"
    " | CMLoadK cm_type"
    " | CMAssignLK cm_expr cm_type"
    " | CMAssignRK cm_value cm_type"
    " | CMBinLK int cm_expr cm_type"
    " | CMBinRK int cm_value cm_type"
    " | CMUnaryK int"
    " | CMIndexLK cm_expr cm_type"
    " | CMIndexRK cm_value cm_type"
    " | CMMemberK int"
    " | CMPutcK | CMPutiK | CMExitK | CMExprStmtK"
    " | CMInitK int"
    " | CMBlockK (int->int->cm_value) (cm_region)list"
    " | CMSeqK cm_stmt"
    " | CMIfK cm_stmt cm_stmt"
    " | CMWhileGuardK cm_expr cm_stmt"
    " | CMWhileBodyK cm_expr cm_stmt (int->int->cm_value) (cm_region)list"
    " | CMReturnK"
    " | CMArgK int (cm_expr)list (cm_value)list cm_type"
    " | CMCallK int (int->int->cm_value) int (cm_region)list cm_type");
PROOF static int _t_cm_frame = cst_add_type_to_header("cm_frame", 0);
PROOF static int _c_CMHaltK = cst_add_const_to_header(`CMHaltK:cm_frame`);
PROOF static int _c_CMLoadK =
    cst_add_const_to_header(`CMLoadK:cm_type->cm_frame`);
PROOF static int _c_CMAssignLK =
    cst_add_const_to_header(`CMAssignLK:cm_expr->cm_type->cm_frame`);
PROOF static int _c_CMAssignRK =
    cst_add_const_to_header(`CMAssignRK:cm_value->cm_type->cm_frame`);
PROOF static int _c_CMBinLK =
    cst_add_const_to_header(`CMBinLK:int->cm_expr->cm_type->cm_frame`);
PROOF static int _c_CMBinRK =
    cst_add_const_to_header(`CMBinRK:int->cm_value->cm_type->cm_frame`);
PROOF static int _c_CMUnaryK =
    cst_add_const_to_header(`CMUnaryK:int->cm_frame`);
PROOF static int _c_CMIndexLK =
    cst_add_const_to_header(`CMIndexLK:cm_expr->cm_type->cm_frame`);
PROOF static int _c_CMIndexRK =
    cst_add_const_to_header(`CMIndexRK:cm_value->cm_type->cm_frame`);
PROOF static int _c_CMMemberK =
    cst_add_const_to_header(`CMMemberK:int->cm_frame`);
PROOF static int _c_CMPutcK = cst_add_const_to_header(`CMPutcK:cm_frame`);
PROOF static int _c_CMPutiK = cst_add_const_to_header(`CMPutiK:cm_frame`);
PROOF static int _c_CMExitK = cst_add_const_to_header(`CMExitK:cm_frame`);
PROOF static int _c_CMExprStmtK =
    cst_add_const_to_header(`CMExprStmtK:cm_frame`);
PROOF static int _c_CMInitK =
    cst_add_const_to_header(`CMInitK:int->cm_frame`);
PROOF static int _c_CMBlockK = cst_add_const_to_header(
    `CMBlockK:(int->int->cm_value)->(cm_region)list->cm_frame`);
PROOF static int _c_CMSeqK =
    cst_add_const_to_header(`CMSeqK:cm_stmt->cm_frame`);
PROOF static int _c_CMIfK =
    cst_add_const_to_header(`CMIfK:cm_stmt->cm_stmt->cm_frame`);
PROOF static int _c_CMWhileGuardK = cst_add_const_to_header(
    `CMWhileGuardK:cm_expr->cm_stmt->cm_frame`);
PROOF static int _c_CMWhileBodyK = cst_add_const_to_header(
    `CMWhileBodyK:cm_expr->cm_stmt->(int->int->cm_value)->
      (cm_region)list->cm_frame`);
PROOF static int _c_CMReturnK =
    cst_add_const_to_header(`CMReturnK:cm_frame`);
PROOF static int _c_CMArgK = cst_add_const_to_header(
    `CMArgK:int->(cm_expr)list->(cm_value)list->cm_type->cm_frame`);
PROOF static int _c_CMCallK = cst_add_const_to_header(
    `CMCallK:int->(int->int->cm_value)->int->(cm_region)list->
      cm_type->cm_frame`);

PROOF indtype cm_task_ty = new_datatype_definition(
    "cm_task = CMStartTask cm_program (int)list"
    " | CMRTask cm_program int cm_expr cm_src_state (cm_frame)list"
    " | CMLTask cm_program int cm_expr cm_src_state (cm_frame)list"
    " | CMSTask cm_program int cm_stmt cm_src_state (cm_frame)list"
    " | CMVTask cm_program int cm_value cm_src_state (cm_frame)list"
    " | CMCTask cm_program int cm_control cm_src_state (cm_frame)list"
    " | CMDoneTask cm_src_state cm_control int");
PROOF thm cm_task_RECURSION = cm_task_ty.rec;
PROOF static int _t_cm_task = cst_add_type_to_header("cm_task", 0);
PROOF static int _c_CMStartTask =
    cst_add_const_to_header(`CMStartTask:cm_program->(int)list->cm_task`);
PROOF static int _c_CMRTask = cst_add_const_to_header(
    `CMRTask:cm_program->int->cm_expr->cm_src_state->
      (cm_frame)list->cm_task`);
PROOF static int _c_CMLTask = cst_add_const_to_header(
    `CMLTask:cm_program->int->cm_expr->cm_src_state->
      (cm_frame)list->cm_task`);
PROOF static int _c_CMSTask = cst_add_const_to_header(
    `CMSTask:cm_program->int->cm_stmt->cm_src_state->
      (cm_frame)list->cm_task`);
PROOF static int _c_CMVTask = cst_add_const_to_header(
    `CMVTask:cm_program->int->cm_value->cm_src_state->
      (cm_frame)list->cm_task`);
PROOF static int _c_CMCTask = cst_add_const_to_header(
    `CMCTask:cm_program->int->cm_control->cm_src_state->
      (cm_frame)list->cm_task`);
PROOF static int _c_CMDoneTask =
    cst_add_const_to_header(
      `CMDoneTask:cm_src_state->cm_control->int->cm_task`);

PROOF indtype cm_outcome_ty = new_datatype_definition(
    "cm_outcome = CMOutcome cm_src_state cm_control int");
PROOF thm cm_outcome_RECURSION = cm_outcome_ty.rec;
PROOF static int _t_cm_outcome = cst_add_type_to_header("cm_outcome", 0);
PROOF static int _c_CMOutcome =
    cst_add_const_to_header(
      `CMOutcome:cm_src_state->cm_control->int->cm_outcome`);

PROOF thm get_cm_control_recursion(void) { return cm_control_ty.rec; }
PROOF thm get_cm_frame_recursion(void) { return cm_frame_ty.rec; }

PROOF thm get_cm_task_recursion(void) { return cm_task_RECURSION; }
PROOF thm get_cm_outcome_recursion(void) { return cm_outcome_RECURSION; }

PROOF thm cm_regions_for_slots_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_regions_for_slots (structs:(cm_struct_d)list)
        ([]:(cm_slot_d)list) (gen:int) (base:int) =
        ([]:(cm_region)list)) &&
     (!slot rest gen base.
        cm_regions_for_slots structs
          ((slot:cm_slot_d) :: (rest:(cm_slot_d)list))
          (gen:int) (base:int) =
        CMRegion gen base 0i (cm_slot_size structs slot) T T ::
        cm_regions_for_slots structs rest (gen + 1i)
          (base + cm_slot_size structs slot))`);
PROOF int _e_cm_regions_for_slots =
    cst_add_const_to_header(`cm_regions_for_slots`);

PROOF thm cm_param_base_def = new_fun_definition(
    `cm_param_base (p:cm_program) (fid:int) (index:int)
       (fp:int) : int =
       fp + 8i +
       cm_slots_prefix (cm_program_structs p)
         (cm_function_params
           (inth fid (cm_program_functions p))) index`);
PROOF thm cm_local_base_def = new_fun_definition(
    `cm_local_base (p:cm_program) (fid:int) (index:int)
       (fp:int) : int =
       fp + 8i +
       cm_slots_size (cm_program_structs p)
         (cm_function_params
           (inth fid (cm_program_functions p))) +
       cm_slots_prefix (cm_program_structs p)
         (cm_function_locals
           (inth fid (cm_program_functions p))) index`);
PROOF int _e_cm_param_base = cst_add_const_to_header(`cm_param_base`);
PROOF int _e_cm_local_base = cst_add_const_to_header(`cm_local_base`);
PROOF thm get_cm_param_base_def(void) { return cm_param_base_def; }
PROOF thm get_cm_local_base_def(void) { return cm_local_base_def; }

PROOF thm cm_call_env_def = new_fun_definition(
    `cm_call_env (p:cm_program) (fid:int)
       (oldenv:int->int->cm_value) (fp:int) (firstgen:int) :
       int->int->cm_value =
       (\scope:int slot:int.
          if scope == 0i then oldenv 0i slot
          else if scope == 2i
               then CMPtrV (firstgen + slot) 0i
                      (cm_slot_size (cm_program_structs p)
                        (inth slot (cm_function_params
                          (inth fid (cm_program_functions p)))))
                      0i
                      (cm_slot_ty
                        (inth slot (cm_function_params
                          (inth fid (cm_program_functions p)))))
               else CMNullV)`);
PROOF int _e_cm_call_env = cst_add_const_to_header(`cm_call_env`);
PROOF thm get_cm_call_env_def(void) { return cm_call_env_def; }

PROOF thm cm_call_base_state_def = new_fun_definition(
    `cm_call_base_state (p:cm_program) (fid:int)
       (st:cm_src_state) : cm_src_state =
       cm_state_make
         (tower_setw (cm_state_mem st)
           (cm_state_fp st -
            cm_frame_size (cm_program_structs p)
              (inth fid (cm_program_functions p)))
           (cm_state_fp st))
         (cm_state_init st) (cm_state_tags st) (cm_state_tagged st)
         (cm_call_env p fid (cm_state_env st)
           (cm_state_fp st -
            cm_frame_size (cm_program_structs p)
              (inth fid (cm_program_functions p)))
           (cm_state_nextgen st))
         (cm_state_input st) (cm_state_output st)
         (cm_state_fp st -
          cm_frame_size (cm_program_structs p)
            (inth fid (cm_program_functions p)))
         (cm_state_nextgen st +
          ilength (cm_function_params
            (inth fid (cm_program_functions p))))
         (APPEND
           (cm_regions_for_slots (cm_program_structs p)
             (cm_function_params
               (inth fid (cm_program_functions p)))
             (cm_state_nextgen st)
             ((cm_state_fp st -
               cm_frame_size (cm_program_structs p)
                 (inth fid (cm_program_functions p))) + 8i))
           (cm_state_regions st))`);
PROOF int _e_cm_call_base_state =
    cst_add_const_to_header(`cm_call_base_state`);
PROOF thm get_cm_call_base_state_def(void) {
  return cm_call_base_state_def;
}

PROOF thm cm_store_params_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_store_params (p:cm_program) (fid:int)
        ([]:(cm_value)list) (index:int) (st:cm_src_state) = st) &&
     (!v rest.
        cm_store_params p fid
          ((v:cm_value) :: (rest:(cm_value)list))
          (index:int) (st:cm_src_state) =
        cm_store_params p fid rest (index + 1i)
          (cm_state_store
            (cm_slot_ty (inth index
              (cm_function_params
                (inth fid (cm_program_functions p)))))
            (cm_state_env st 2i index) v st))`);
PROOF int _e_cm_store_params = cst_add_const_to_header(`cm_store_params`);
PROOF thm get_cm_store_params_def(void) { return cm_store_params_def; }

PROOF thm cm_enter_call_def = new_fun_definition(
    `cm_enter_call (p:cm_program) (fid:int)
       (values:(cm_value)list) (st:cm_src_state) : cm_src_state =
       cm_store_params p fid values 0i (cm_call_base_state p fid st)`);
PROOF int _e_cm_enter_call = cst_add_const_to_header(`cm_enter_call`);
PROOF thm get_cm_enter_call_def(void) { return cm_enter_call_def; }

PROOF thm cm_activate_local_def = new_fun_definition(
    `cm_activate_local (p:cm_program) (fid:int) (slot:int)
       (st:cm_src_state) : cm_src_state =
       cm_state_make (cm_state_mem st)
         (cm_clear_init (cm_state_init st)
           (cm_local_base p fid slot (cm_state_fp st))
           (cm_slot_size (cm_program_structs p)
             (inth slot (cm_function_locals
               (inth fid (cm_program_functions p))))))
         (cm_state_tags st)
         (cm_clear_tagged (cm_state_tagged st)
           (cm_local_base p fid slot (cm_state_fp st))
           (cm_slot_size (cm_program_structs p)
             (inth slot (cm_function_locals
               (inth fid (cm_program_functions p))))))
         (\scope:int index:int.
            if scope == 1i && index == slot
            then CMPtrV (cm_state_nextgen st) 0i
                   (cm_slot_size (cm_program_structs p)
                     (inth slot (cm_function_locals
                       (inth fid (cm_program_functions p)))))
                   0i
                   (cm_slot_ty
                     (inth slot (cm_function_locals
                       (inth fid (cm_program_functions p)))))
            else cm_state_env st scope index)
         (cm_state_input st) (cm_state_output st) (cm_state_fp st)
         (cm_state_nextgen st + 1i)
         (CMRegion (cm_state_nextgen st)
            (cm_local_base p fid slot (cm_state_fp st)) 0i
            (cm_slot_size (cm_program_structs p)
              (inth slot (cm_function_locals
                (inth fid (cm_program_functions p)))))
            T T :: cm_state_regions st)`);
PROOF int _e_cm_activate_local =
    cst_add_const_to_header(`cm_activate_local`);
PROOF thm get_cm_activate_local_def(void) {
  return cm_activate_local_def;
}

PROOF thm cm_retire_region_def = new_rec_definition(
    cm_region_ty.rec,
    `cm_retire_region
       (CMRegion (gen:int) (base:int) (lo:int) (hi:int)
          (writable:bool) (live:bool)) =
       CMRegion gen base lo hi writable F`);
PROOF thm cm_restore_regions_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!old.
        cm_restore_regions ([]:(cm_region)list)
          (old:(cm_region)list) = old) &&
     (!region rest old.
        cm_restore_regions
          ((region:cm_region) :: (rest:(cm_region)list))
          (old:(cm_region)list) =
        (if region :: rest == old
         then old
         else cm_retire_region region ::
              cm_restore_regions rest old))`);
PROOF int _e_cm_restore_regions =
    cst_add_const_to_header(`cm_restore_regions`);

PROOF thm cm_restore_init_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!all old init.
        cm_restore_init (all:(cm_region)list)
          ([]:(cm_region)list) (old:(cm_region)list)
          (init:int->bool) = init) &&
     (!all region rest old init.
        cm_restore_init (all:(cm_region)list)
          ((region:cm_region) :: (rest:(cm_region)list))
          (old:(cm_region)list) (init:int->bool) =
        (if region :: rest == old
         then init
         else cm_restore_init all rest old
                (if cm_region_live region
                 then cm_clear_init init
                        (cm_region_base all
                           (cm_region_gen region) +
                         cm_region_lo region)
                        (cm_region_hi region -
                         cm_region_lo region)
                 else init)))`);
PROOF thm cm_restore_tagged_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!all old tagged.
        cm_restore_tagged (all:(cm_region)list)
          ([]:(cm_region)list) (old:(cm_region)list)
          (tagged:int->bool) = tagged) &&
     (!all region rest old tagged.
        cm_restore_tagged (all:(cm_region)list)
          ((region:cm_region) :: (rest:(cm_region)list))
          (old:(cm_region)list) (tagged:int->bool) =
        (if region :: rest == old
         then tagged
         else cm_restore_tagged all rest old
                (if cm_region_live region
                 then cm_clear_tagged tagged
                        (cm_region_base all
                           (cm_region_gen region) +
                         cm_region_lo region)
                        (cm_region_hi region -
                         cm_region_lo region)
                 else tagged)))`);
PROOF int _e_cm_restore_init =
    cst_add_const_to_header(`cm_restore_init`);
PROOF int _e_cm_restore_tagged =
    cst_add_const_to_header(`cm_restore_tagged`);

PROOF thm cm_restore_scope_def = new_fun_definition(
    `cm_restore_scope (st:cm_src_state)
       (oldenv:int->int->cm_value)
       (oldregions:(cm_region)list) : cm_src_state =
       cm_state_make (cm_state_mem st)
         (cm_restore_init (cm_state_regions st)
           (cm_state_regions st) oldregions (cm_state_init st))
         (cm_state_tags st)
         (cm_restore_tagged (cm_state_regions st)
           (cm_state_regions st) oldregions (cm_state_tagged st)) oldenv
         (cm_state_input st) (cm_state_output st) (cm_state_fp st)
         (cm_state_nextgen st)
         (cm_restore_regions (cm_state_regions st) oldregions)`);
PROOF int _e_cm_restore_scope =
    cst_add_const_to_header(`cm_restore_scope`);
PROOF thm get_cm_restore_scope_def(void) {
  return cm_restore_scope_def;
}

PROOF thm cm_restore_call_def = new_fun_definition(
    `cm_restore_call (st:cm_src_state)
       (oldenv:int->int->cm_value) (oldfp:int)
       (oldregions:(cm_region)list) : cm_src_state =
       cm_state_make (cm_state_mem st)
         (cm_restore_init (cm_state_regions st)
           (cm_state_regions st) oldregions (cm_state_init st))
         (cm_state_tags st)
         (cm_restore_tagged (cm_state_regions st)
           (cm_state_regions st) oldregions (cm_state_tagged st)) oldenv
         (cm_state_input st) (cm_state_output st) oldfp
         (cm_state_nextgen st)
         (cm_restore_regions (cm_state_regions st) oldregions)`);
PROOF int _e_cm_restore_call = cst_add_const_to_header(`cm_restore_call`);
PROOF thm get_cm_restore_call_def(void) {
  return cm_restore_call_def;
}

PROOF thm cm_is_call_frame_def = new_rec_definition(
    cm_frame_ty.rec,
    `(cm_is_call_frame CMHaltK = F) &&
     (!ty. cm_is_call_frame (CMLoadK (ty:cm_type)) = F) &&
     (!expr ty.
        cm_is_call_frame (CMAssignLK (expr:cm_expr) (ty:cm_type)) = F) &&
     (!value ty.
        cm_is_call_frame (CMAssignRK (value:cm_value) (ty:cm_type)) = F) &&
     (!op expr ty.
        cm_is_call_frame
          (CMBinLK (op:int) (expr:cm_expr) (ty:cm_type)) = F) &&
     (!op value ty.
        cm_is_call_frame
          (CMBinRK (op:int) (value:cm_value) (ty:cm_type)) = F) &&
     (!op. cm_is_call_frame (CMUnaryK (op:int)) = F) &&
     (!expr ty.
        cm_is_call_frame
          (CMIndexLK (expr:cm_expr) (ty:cm_type)) = F) &&
     (!value ty.
        cm_is_call_frame
          (CMIndexRK (value:cm_value) (ty:cm_type)) = F) &&
     (!mid. cm_is_call_frame (CMMemberK (mid:int)) = F) &&
     (cm_is_call_frame CMPutcK = F) &&
     (cm_is_call_frame CMPutiK = F) &&
     (cm_is_call_frame CMExitK = F) &&
     (cm_is_call_frame CMExprStmtK = F) &&
     (!slot. cm_is_call_frame (CMInitK (slot:int)) = F) &&
     (!env regions.
        cm_is_call_frame
          (CMBlockK (env:int->int->cm_value)
             (regions:(cm_region)list)) = F) &&
     (!stmt. cm_is_call_frame (CMSeqK (stmt:cm_stmt)) = F) &&
     (!yes no.
        cm_is_call_frame (CMIfK (yes:cm_stmt) (no:cm_stmt)) = F) &&
     (!guard body.
        cm_is_call_frame
          (CMWhileGuardK (guard:cm_expr) (body:cm_stmt)) = F) &&
     (!guard body env regions.
        cm_is_call_frame
          (CMWhileBodyK (guard:cm_expr) (body:cm_stmt)
             (env:int->int->cm_value) (regions:(cm_region)list)) = F) &&
     (cm_is_call_frame CMReturnK = F) &&
     (!callee rest values ret.
        cm_is_call_frame
          (CMArgK (callee:int) (rest:(cm_expr)list)
             (values:(cm_value)list) (ret:cm_type)) = F) &&
     (!caller env fp regions ret.
        cm_is_call_frame
          (CMCallK (caller:int) (env:int->int->cm_value) (fp:int)
             (regions:(cm_region)list) (ret:cm_type)) = T)`);
PROOF int _e_cm_is_call_frame =
    cst_add_const_to_header(`cm_is_call_frame`);

PROOF thm cm_call_depth_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_call_depth ([]:(cm_frame)list) = 0i) &&
     (!frame rest.
        cm_call_depth ((frame:cm_frame) :: (rest:(cm_frame)list)) =
          (if cm_is_call_frame frame then 1i else 0i) +
          cm_call_depth rest)`);
PROOF int _e_cm_call_depth = cst_add_const_to_header(`cm_call_depth`);

PROOF thm cm_call_ok_def = new_fun_definition(
    `cm_call_ok (p:cm_program) (fid:int)
       (values:(cm_value)list) (st:cm_src_state) : bool =
       (0i <= fid && fid < ilength (cm_program_functions p) &&
        ilength values ==
          ilength (cm_function_params
            (inth fid (cm_program_functions p))) &&
        8i <= cm_frame_size (cm_program_structs p)
          (inth fid (cm_program_functions p)) &&
        cm_static_size p <=
          cm_state_fp st -
            cm_frame_size (cm_program_structs p)
              (inth fid (cm_program_functions p)) &&
        cm_state_fp st <= 1048576i &&
        tower_word_valid
          (cm_state_fp st -
            cm_frame_size (cm_program_structs p)
              (inth fid (cm_program_functions p))))`);
PROOF int _e_cm_call_ok = cst_add_const_to_header(`cm_call_ok`);

PROOF thm cm_begin_call_def = new_fun_definition(
    `cm_begin_call (p:cm_program) (caller:int) (fid:int)
       (values:(cm_value)list) (st:cm_src_state) (ret:cm_type)
       (ks:(cm_frame)list) : cm_task =
       (if cm_call_ok p fid values st && cm_call_depth ks < 65536i
        then CMSTask p fid
          (cm_function_body (inth fid (cm_program_functions p)))
          (cm_enter_call p fid values st)
          (CMCallK caller (cm_state_env st) (cm_state_fp st)
             (cm_state_regions st) ret :: ks)
        else CMCTask p caller (CMError 1i) st ks)`);
PROOF int _e_cm_begin_call = cst_add_const_to_header(`cm_begin_call`);

PROOF thm cm_binding_array_def = new_fun_definition(
    `cm_binding_array (p:cm_program) (fid:int)
       (scope:int) (slot:int) : bool =
       (if scope == 0i
        then ~(cm_global_count (inth slot (cm_program_globals p)) == 0i)
        else if scope == 1i
             then ~(cm_slot_count
               (inth slot (cm_function_locals
                 (inth fid (cm_program_functions p)))) == 0i)
             else F)`);
PROOF int _e_cm_binding_array =
    cst_add_const_to_header(`cm_binding_array`);

PROOF thm cm_member_slot_def = new_fun_definition(
    `cm_member_slot (p:cm_program) (ptr:cm_value)
       (mid:int) : cm_slot_d =
       inth mid (cm_struct_members
         (inth (cm_struct_id (cm_ptr_view ptr))
           (cm_program_structs p)))`);
PROOF thm cm_member_array_def = new_fun_definition(
    `cm_member_array (p:cm_program) (base:cm_type)
       (mid:int) : bool =
       ~(cm_slot_count
         (inth mid (cm_struct_members
           (inth (cm_struct_id (cm_pointee base))
             (cm_program_structs p)))) == 0i)`);
PROOF int _e_cm_member_slot =
    cst_add_const_to_header(`cm_member_slot`);
PROOF int _e_cm_member_array =
    cst_add_const_to_header(`cm_member_array`);

PROOF thm cm_ptr_member_def = new_fun_definition(
    `cm_ptr_member (p:cm_program) (ptr:cm_value)
       (mid:int) : cm_value =
       CMPtrV (cm_ptr_gen ptr)
         (cm_ptr_offset ptr +
          cm_member_offset (cm_program_structs p)
            (cm_struct_id (cm_ptr_view ptr)) mid)
         (cm_ptr_offset ptr +
          cm_member_offset (cm_program_structs p)
            (cm_struct_id (cm_ptr_view ptr)) mid +
          cm_slot_size (cm_program_structs p)
            (cm_member_slot p ptr mid))
         (cm_ptr_offset ptr +
          cm_member_offset (cm_program_structs p)
            (cm_struct_id (cm_ptr_view ptr)) mid)
         (cm_slot_ty (cm_member_slot p ptr mid))`);
PROOF thm cm_ptr_member_ok_def = new_fun_definition(
    `cm_ptr_member_ok (p:cm_program) (ptr:cm_value)
       (mid:int) (st:cm_src_state) : bool =
       (cm_pointer_live st ptr &&
        cm_ptr_lo ptr <= cm_ptr_lo (cm_ptr_member p ptr mid) &&
        cm_ptr_hi (cm_ptr_member p ptr mid) <= cm_ptr_hi ptr &&
        cm_pointer_live st (cm_ptr_member p ptr mid))`);
PROOF int _e_cm_ptr_member = cst_add_const_to_header(`cm_ptr_member`);
PROOF int _e_cm_ptr_member_ok =
    cst_add_const_to_header(`cm_ptr_member_ok`);
PROOF thm cm_binding_address_ok_def = new_fun_definition(
    `cm_binding_address_ok (p:cm_program) (fid:int)
       (scope:int) (slot:int) (st:cm_src_state) : bool =
       (tower_signed64
          (if scope == 0i then cm_global_address p slot
           else if scope == 1i
                then cm_local_base p fid slot (cm_state_fp st)
                else cm_param_base p fid slot (cm_state_fp st)) &&
        tower_wrap64
          (if scope == 0i then cm_global_address p slot
           else if scope == 1i
                then cm_local_base p fid slot (cm_state_fp st)
                else cm_param_base p fid slot (cm_state_fp st)) ==
        cm_value_number st
          (if scope == 0i then cm_global_pointer p slot
           else cm_state_env st scope slot) &&
        cm_value_type
          (if scope == 0i then cm_global_pointer p slot
           else cm_state_env st scope slot) ==
        CMPtrTy
          (if scope == 0i
           then cm_global_ty (inth slot (cm_program_globals p))
           else if scope == 1i
                then cm_slot_ty
                  (inth slot
                    (cm_function_locals
                      (inth fid (cm_program_functions p))))
                else cm_slot_ty
                  (inth slot
                    (cm_function_params
                      (inth fid (cm_program_functions p))))))`);
PROOF int _e_cm_binding_address_ok =
    cst_add_const_to_header(`cm_binding_address_ok`);


PROOF thm cm_rstart_def = new_rec_definition(cm_expr_RECURSION,
    `(cm_rstart (p:cm_program) (fid:int)
        (CMConstE (n:int) (ty:cm_type)) (st:cm_src_state)
        (ks:(cm_frame)list) =
        CMVTask p fid (cm_convert_value st ty (CMIntV n)) st ks) &&
     (cm_rstart p fid
        (CMStringE (sid:int) (ty:cm_type)) st ks =
        CMVTask p fid (cm_string_pointer p sid) st ks) &&
     (cm_rstart p fid
        (CMVarE (scope:int) (slot:int) (ty:cm_type)) st ks =
        (if cm_binding_array p fid scope slot
         then if cm_binding_address_ok p fid scope slot st
              then CMVTask p fid
                (if scope == 0i
                 then cm_global_pointer p slot
                 else cm_state_env st scope slot) st ks
              else CMCTask p fid (CMError 1i) st ks
         else CMLTask p fid (CMVarE scope slot ty) st
                (CMLoadK ty :: ks))) &&
     (!dst src ty.
        cm_rstart p fid
          (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type))
          st ks =
        CMLTask p fid dst st (CMAssignLK src ty :: ks)) &&
     (!op left right ty.
        cm_rstart p fid
          (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
             (ty:cm_type)) st ks =
        CMRTask p fid left st (CMBinLK op right ty :: ks)) &&
     (!op arg ty.
        cm_rstart p fid
          (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) st ks =
        (if op == 2i
         then CMRTask p fid arg st (CMLoadK ty :: ks)
         else if op == 3i
              then CMLTask p fid arg st ks
              else CMRTask p fid arg st (CMUnaryK op :: ks))) &&
     (!base index ty.
        cm_rstart p fid
          (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type))
          st ks =
        CMLTask p fid (CMIndexE base index ty) st
          (CMLoadK ty :: ks)) &&
     (!base mid ty.
        cm_rstart p fid
          (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) st ks =
        CMLTask p fid (CMMemberE base mid ty) st
          (if cm_member_array p (cm_expr_type base) mid
           then ks else CMLoadK ty :: ks)) &&
     (!callee args ty.
        cm_rstart p fid
          (CMCallE (callee:int) (args:(cm_expr)list) (ty:cm_type))
          st ks =
        cm_args_start p fid args st ks callee ty) &&
     (!asked ty.
        cm_rstart p fid
          (CMSizeofE (asked:cm_type) (ty:cm_type)) st ks =
        CMVTask p fid
          (CMIntV (cm_type_size (cm_program_structs p) asked)) st ks) &&
     (!ty.
        cm_rstart p fid (CMGetcE (ty:cm_type)) st ks =
        (if cm_state_input st == []
         then CMVTask p fid (CMIntV (--1i)) st ks
         else if tower_byte_value (HD (cm_state_input st))
              then CMVTask p fid (CMIntV (HD (cm_state_input st)))
                     (cm_state_io st (TL (cm_state_input st))
                       (cm_state_output st)) ks
              else CMCTask p fid (CMError 1i) st ks)) &&
     (!arg ty.
        cm_rstart p fid (CMPutcE (arg:cm_expr) (ty:cm_type)) st ks =
        CMRTask p fid arg st (CMPutcK :: ks)) &&
     (!arg ty.
        cm_rstart p fid (CMPutiE (arg:cm_expr) (ty:cm_type)) st ks =
        CMRTask p fid arg st (CMPutiK :: ks)) &&
     (!arg ty.
        cm_rstart p fid (CMExitE (arg:cm_expr) (ty:cm_type)) st ks =
        CMRTask p fid arg st (CMExitK :: ks)) &&
     (cm_args_start (p:cm_program) (caller:int)
        ([]:(cm_expr)list) (st:cm_src_state) (ks:(cm_frame)list)
        (callee:int) (ret:cm_type) =
        cm_begin_call p caller callee [] st ret ks) &&
     (!arg args.
        cm_args_start p caller
          ((arg:cm_expr) :: (args:(cm_expr)list))
          st ks callee ret =
        CMRTask p caller arg st (CMArgK callee args [] ret :: ks))`);
PROOF int _e_cm_rstart = cst_add_const_to_header(`cm_rstart`);
PROOF int _e_cm_args_start = cst_add_const_to_header(`cm_args_start`);

PROOF thm cm_lstart_def = new_rec_definition(cm_expr_RECURSION,
    `(cm_lstart (p:cm_program) (fid:int)
        (CMConstE (n:int) (ty:cm_type)) (st:cm_src_state)
        (ks:(cm_frame)list) =
        CMCTask p fid (CMError 1i) st ks) &&
     (cm_lstart p fid (CMStringE (sid:int) (ty:cm_type)) st ks =
        CMCTask p fid (CMError 1i) st ks) &&
     (cm_lstart p fid
        (CMVarE (scope:int) (slot:int) (ty:cm_type)) st ks =
        (if cm_binding_address_ok p fid scope slot st
         then CMVTask p fid
           (if scope == 0i then cm_global_pointer p slot
            else cm_state_env st scope slot) st ks
         else CMCTask p fid (CMError 1i) st ks)) &&
     (!dst src ty.
        cm_lstart p fid (CMAssignE dst src ty) st ks =
        CMCTask p fid (CMError 1i) st ks) &&
     (!op left right ty.
        cm_lstart p fid (CMBinaryE op left right ty) st ks =
        CMCTask p fid (CMError 1i) st ks) &&
     (!op arg ty.
        cm_lstart p fid (CMUnaryE (op:int) (arg:cm_expr) ty) st ks =
        (if op == 2i then CMRTask p fid arg st ks
         else CMCTask p fid (CMError 1i) st ks)) &&
     (!base index ty.
        cm_lstart p fid
          (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type))
          st ks =
        CMRTask p fid base st (CMIndexLK index ty :: ks)) &&
     (!base mid ty.
        cm_lstart p fid
          (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) st ks =
        CMRTask p fid base st (CMMemberK mid :: ks)) &&
     (!callee args ty.
        cm_lstart p fid (CMCallE callee args ty) st ks =
        CMCTask p fid (CMError 1i) st ks) &&
     (!asked ty.
        cm_lstart p fid (CMSizeofE asked ty) st ks =
        CMCTask p fid (CMError 1i) st ks) &&
     (!ty. cm_lstart p fid (CMGetcE ty) st ks =
        CMCTask p fid (CMError 1i) st ks) &&
     (!arg ty. cm_lstart p fid (CMPutcE arg ty) st ks =
        CMCTask p fid (CMError 1i) st ks) &&
     (!arg ty. cm_lstart p fid (CMPutiE arg ty) st ks =
        CMCTask p fid (CMError 1i) st ks) &&
     (!arg ty. cm_lstart p fid (CMExitE arg ty) st ks =
        CMCTask p fid (CMError 1i) st ks) &&
     (cm_lstart_list (p:cm_program) (fid:int)
        ([]:(cm_expr)list) (st:cm_src_state) (ks:(cm_frame)list) =
        CMCTask p fid (CMError 1i) st ks) &&
     (!arg args.
        cm_lstart_list p fid
          ((arg:cm_expr) :: (args:(cm_expr)list)) st ks =
        CMCTask p fid (CMError 1i) st ks)`);
PROOF int _e_cm_lstart = cst_add_const_to_header(`cm_lstart`);

PROOF thm cm_control_kind_def = new_rec_definition(cm_control_ty.rec,
    `(cm_control_kind CMNormal = 0i) &&
     (cm_control_kind CMBreak = 1i) &&
     (cm_control_kind CMContinue = 2i) &&
     (!v. cm_control_kind (CMReturn (v:cm_value)) = 3i) &&
     (!status. cm_control_kind (CMExit (status:int)) = 4i) &&
     (!code. cm_control_kind (CMError (code:int)) = 5i)`);
PROOF thm cm_control_value_def = new_rec_definition(cm_control_ty.rec,
    `(cm_control_value CMNormal = CMIntV 0i) &&
     (cm_control_value CMBreak = CMIntV 0i) &&
     (cm_control_value CMContinue = CMIntV 0i) &&
     (!v. cm_control_value (CMReturn (v:cm_value)) = v) &&
     (!status. cm_control_value (CMExit (status:int)) = CMIntV status) &&
     (!code. cm_control_value (CMError (code:int)) = CMIntV code)`);
PROOF thm cm_control_status_def = new_rec_definition(cm_control_ty.rec,
    `(cm_control_status CMNormal = 0i) &&
     (cm_control_status CMBreak = 2i) &&
     (cm_control_status CMContinue = 2i) &&
     (!v. cm_control_status (CMReturn (v:cm_value)) = 0i) &&
     (!status. cm_control_status (CMExit (status:int)) = status) &&
     (!code. cm_control_status (CMError (code:int)) = 2i)`);
PROOF int _e_cm_control_kind =
    cst_add_const_to_header(`cm_control_kind`);
PROOF int _e_cm_control_value =
    cst_add_const_to_header(`cm_control_value`);
PROOF int _e_cm_control_status =
    cst_add_const_to_header(`cm_control_status`);

PROOF thm cm_local_slot_ok_def = new_fun_definition(
    `cm_local_slot_ok (p:cm_program) (fid:int) (slot:int) : bool =
       (0i <= fid && fid < ilength (cm_program_functions p) &&
        0i <= slot &&
        slot < ilength
          (cm_function_locals
            (inth fid (cm_program_functions p))))`);
PROOF int _e_cm_local_slot_ok =
    cst_add_const_to_header(`cm_local_slot_ok`);
PROOF thm get_cm_local_slot_ok_def(void) {
  return cm_local_slot_ok_def;
}
PROOF thm cm_stmt_start_safe_def = new_rec_definition(
    cm_stmt_RECURSION,
    `(cm_stmt_start_safe (p:cm_program) (fid:int) CMSkipS = T) &&
     (!expr. cm_stmt_start_safe p fid (CMExprS (expr:cm_expr)) = T) &&
     (!slot.
        cm_stmt_start_safe p fid (CMDeclS (slot:int)) =
          cm_local_slot_ok p fid slot) &&
     (!slot expr.
        cm_stmt_start_safe p fid
          (CMInitS (slot:int) (expr:cm_expr)) =
          cm_local_slot_ok p fid slot) &&
     (!first second.
        cm_stmt_start_safe p fid
          (CMSeqS (first:cm_stmt) (second:cm_stmt)) = T) &&
     (!body.
        cm_stmt_start_safe p fid (CMBlockS (body:cm_stmt)) = T) &&
     (!guard yes no.
        cm_stmt_start_safe p fid
          (CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)) = T) &&
     (!guard body.
        cm_stmt_start_safe p fid
          (CMWhileS (guard:cm_expr) (body:cm_stmt)) = T) &&
     (cm_stmt_start_safe p fid CMBreakS = T) &&
     (cm_stmt_start_safe p fid CMContinueS = T) &&
     (!expr.
        cm_stmt_start_safe p fid
          (CMReturnS (expr:cm_expr)) = T)`);
PROOF int _e_cm_stmt_start_safe =
    cst_add_const_to_header(`cm_stmt_start_safe`);
PROOF thm get_cm_stmt_start_safe_def(void) {
  return cm_stmt_start_safe_def;
}


PROOF thm cm_sstart_def = new_rec_definition(cm_stmt_RECURSION,
    `(cm_sstart (p:cm_program) (fid:int) CMSkipS
        (st:cm_src_state) (ks:(cm_frame)list) =
        CMCTask p fid CMNormal st ks) &&
     (!expr.
        cm_sstart p fid (CMExprS (expr:cm_expr)) st ks =
        CMRTask p fid expr st (CMExprStmtK :: ks)) &&
     (!slot.
        cm_sstart p fid (CMDeclS (slot:int)) st ks =
        (if cm_local_slot_ok p fid slot
         then CMCTask p fid CMNormal
                (cm_activate_local p fid slot st) ks
         else CMCTask p fid (CMError 1i) st ks)) &&
     (!slot expr.
        cm_sstart p fid
          (CMInitS (slot:int) (expr:cm_expr)) st ks =
        (if cm_local_slot_ok p fid slot
         then CMRTask p fid expr (cm_activate_local p fid slot st)
                (CMInitK slot :: ks)
         else CMCTask p fid (CMError 1i) st ks)) &&
     (!first second.
        cm_sstart p fid
          (CMSeqS (first:cm_stmt) (second:cm_stmt)) st ks =
        CMSTask p fid first st (CMSeqK second :: ks)) &&
     (!body.
        cm_sstart p fid (CMBlockS (body:cm_stmt)) st ks =
        CMSTask p fid body st
          (CMBlockK (cm_state_env st) (cm_state_regions st) :: ks)) &&
     (!guard yes no.
        cm_sstart p fid
          (CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)) st ks =
        CMRTask p fid guard st (CMIfK yes no :: ks)) &&
     (!guard body.
        cm_sstart p fid
          (CMWhileS (guard:cm_expr) (body:cm_stmt)) st ks =
        CMRTask p fid guard st (CMWhileGuardK guard body :: ks)) &&
     (cm_sstart p fid CMBreakS st ks =
        CMCTask p fid CMBreak st ks) &&
     (cm_sstart p fid CMContinueS st ks =
        CMCTask p fid CMContinue st ks) &&
     (!expr.
        cm_sstart p fid (CMReturnS (expr:cm_expr)) st ks =
        CMRTask p fid expr st (CMReturnK :: ks))`);
PROOF int _e_cm_sstart = cst_add_const_to_header(`cm_sstart`);

PROOF thm cm_vapply_def = new_rec_definition(cm_frame_ty.rec,
    `(cm_vapply (p:cm_program) (fid:int) CMHaltK
        (v:cm_value) (st:cm_src_state) (ks:(cm_frame)list) =
        CMDoneTask st (CMReturn v)
          (tower_status (cm_value_number st v))) &&
     (!ty.
        cm_vapply p fid (CMLoadK (ty:cm_type)) v st ks =
        (if cm_load_ok ty v st
         then CMVTask p fid (cm_load_value ty v st) st ks
         else CMCTask p fid (CMError 1i) st ks)) &&
     (!src ty.
        cm_vapply p fid
          (CMAssignLK (src:cm_expr) (ty:cm_type)) v st ks =
        CMRTask p fid src st (CMAssignRK v ty :: ks)) &&
     (!ptr ty.
        cm_vapply p fid
          (CMAssignRK (ptr:cm_value) (ty:cm_type)) v st ks =
        (if cm_store_ok ty ptr st
         then CMVTask p fid (cm_convert_value st ty v)
                (cm_state_store ty ptr v st) ks
         else CMCTask p fid (CMError 1i) st ks)) &&
     (!op right ty.
        cm_vapply p fid
          (CMBinLK (op:int) (right:cm_expr) (ty:cm_type)) v st ks =
        (if op == 0i && cm_truth st v
         then CMVTask p fid (CMIntV 1i) st ks
         else if op == 1i && ~(cm_truth st v)
              then CMVTask p fid (CMIntV 0i) st ks
              else CMRTask p fid right st (CMBinRK op v ty :: ks))) &&
     (!op left ty.
        cm_vapply p fid
          (CMBinRK (op:int) (left:cm_value) (ty:cm_type)) v st ks =
        (if cm_binary_ok p op left v st
         then CMVTask p fid
                (cm_binary_value p op left v ty st) st ks
         else CMCTask p fid (CMError 1i) st ks)) &&
     (!op.
        cm_vapply p fid (CMUnaryK (op:int)) v st ks =
        CMVTask p fid (cm_unary_value op v st) st ks) &&
     (!index ty.
        cm_vapply p fid
          (CMIndexLK (index:cm_expr) (ty:cm_type)) v st ks =
        CMRTask p fid index st (CMIndexRK v ty :: ks)) &&
     (!base ty.
        cm_vapply p fid
          (CMIndexRK (base:cm_value) (ty:cm_type)) v st ks =
        (if cm_ptr_shift_ok (cm_program_structs p) base
              (cm_value_number st v) st
         then CMVTask p fid
                (cm_ptr_add (cm_program_structs p) base
                  (cm_value_number st v)) st ks
         else CMCTask p fid (CMError 1i) st ks)) &&
     (!mid.
        cm_vapply p fid (CMMemberK (mid:int)) v st ks =
        (if cm_ptr_member_ok p v mid st
         then CMVTask p fid (cm_ptr_member p v mid) st ks
         else CMCTask p fid (CMError 1i) st ks)) &&
     (cm_vapply p fid CMPutcK v st ks =
        CMVTask p fid (CMIntV (cm_value_number st v))
          (cm_state_io st (cm_state_input st)
            (APPEND (cm_state_output st)
              [tower_u8 (cm_value_number st v)])) ks) &&
     (cm_vapply p fid CMPutiK v st ks =
        CMVTask p fid (CMIntV (cm_value_number st v))
          (cm_state_io st (cm_state_input st)
            (APPEND (cm_state_output st)
              (tower_decimal (cm_value_number st v)))) ks) &&
     (cm_vapply p fid CMExitK v st ks =
        CMCTask p fid
          (CMExit (tower_status (cm_value_number st v))) st ks) &&
     (cm_vapply p fid CMExprStmtK v st ks =
        CMCTask p fid CMNormal st ks) &&
     (!slot.
        cm_vapply p fid (CMInitK (slot:int)) v st ks =
        (if cm_binding_address_ok p fid 1i slot st &&
            cm_store_ok
              (cm_slot_ty (inth slot (cm_function_locals
                (inth fid (cm_program_functions p)))))
              (cm_state_env st 1i slot) st
         then CMCTask p fid CMNormal
                (cm_state_store
                  (cm_slot_ty (inth slot (cm_function_locals
                    (inth fid (cm_program_functions p)))))
                  (cm_state_env st 1i slot) v st) ks
         else CMCTask p fid (CMError 1i) st ks)) &&
     (!oldenv oldregions.
        cm_vapply p fid
          (CMBlockK (oldenv:int->int->cm_value)
             (oldregions:(cm_region)list)) v st ks =
        CMCTask p fid (CMError 1i)
          (cm_restore_scope st oldenv oldregions) ks) &&
     (!second.
        cm_vapply p fid (CMSeqK (second:cm_stmt)) v st ks =
        CMCTask p fid (CMError 1i) st ks) &&
     (!yes no.
        cm_vapply p fid
          (CMIfK (yes:cm_stmt) (no:cm_stmt)) v st ks =
        (if cm_truth st v
         then CMSTask p fid yes st
                (CMBlockK (cm_state_env st) (cm_state_regions st) :: ks)
         else CMSTask p fid no st
                (CMBlockK (cm_state_env st)
                  (cm_state_regions st) :: ks))) &&
     (!guard body.
        cm_vapply p fid
          (CMWhileGuardK (guard:cm_expr) (body:cm_stmt)) v st ks =
        (if cm_truth st v
         then CMSTask p fid body st
                (CMWhileBodyK guard body
                  (cm_state_env st) (cm_state_regions st) :: ks)
         else CMCTask p fid CMNormal st ks)) &&
     (!guard body oldenv oldregions.
        cm_vapply p fid
          (CMWhileBodyK (guard:cm_expr) (body:cm_stmt)
             (oldenv:int->int->cm_value)
             (oldregions:(cm_region)list)) v st ks =
        CMCTask p fid (CMError 1i)
          (cm_restore_scope st oldenv oldregions) ks) &&
     (cm_vapply p fid CMReturnK v st ks =
        CMCTask p fid (CMReturn v) st ks) &&
     (!callee rest values ret.
        cm_vapply p fid
          (CMArgK (callee:int) (rest:(cm_expr)list)
             (values:(cm_value)list) (ret:cm_type)) v st ks =
        (if rest == []
         then cm_begin_call p fid callee
                (REVERSE (v :: values)) st ret ks
         else CMRTask p fid (HD rest) st
                (CMArgK callee (TL rest) (v :: values) ret :: ks))) &&
     (!caller oldenv oldfp oldregions ret.
        cm_vapply p fid
          (CMCallK (caller:int) (oldenv:int->int->cm_value)
             (oldfp:int) (oldregions:(cm_region)list)
             (ret:cm_type)) v st ks =
        CMCTask p fid (CMError 1i) st ks)`);
PROOF int _e_cm_vapply = cst_add_const_to_header(`cm_vapply`);

PROOF thm cm_capply_def = new_rec_definition(cm_frame_ty.rec,
    `(cm_capply (p:cm_program) (fid:int) CMHaltK
        (ctl:cm_control) (st:cm_src_state) (ks:(cm_frame)list) =
        (if cm_control_kind ctl == 4i
         then CMDoneTask st ctl (cm_control_status ctl)
         else if cm_control_kind ctl == 3i
              then CMDoneTask st ctl
                (tower_status
                  (cm_value_number st (cm_control_value ctl)))
              else if cm_control_kind ctl == 0i
                   then CMDoneTask st ctl 0i
                   else CMDoneTask st ctl 2i)) &&
     (!ty.
        cm_capply p fid (CMLoadK (ty:cm_type)) ctl st ks =
        CMCTask p fid ctl st ks) &&
     (!src ty.
        cm_capply p fid (CMAssignLK (src:cm_expr) (ty:cm_type))
          ctl st ks = CMCTask p fid ctl st ks) &&
     (!ptr ty.
        cm_capply p fid (CMAssignRK (ptr:cm_value) (ty:cm_type))
          ctl st ks = CMCTask p fid ctl st ks) &&
     (!op right ty.
        cm_capply p fid
          (CMBinLK (op:int) (right:cm_expr) (ty:cm_type))
          ctl st ks = CMCTask p fid ctl st ks) &&
     (!op left ty.
        cm_capply p fid
          (CMBinRK (op:int) (left:cm_value) (ty:cm_type))
          ctl st ks = CMCTask p fid ctl st ks) &&
     (!op. cm_capply p fid (CMUnaryK (op:int)) ctl st ks =
        CMCTask p fid ctl st ks) &&
     (!index ty.
        cm_capply p fid
          (CMIndexLK (index:cm_expr) (ty:cm_type))
          ctl st ks = CMCTask p fid ctl st ks) &&
     (!base ty.
        cm_capply p fid
          (CMIndexRK (base:cm_value) (ty:cm_type))
          ctl st ks = CMCTask p fid ctl st ks) &&
     (!mid.
        cm_capply p fid (CMMemberK (mid:int))
          ctl st ks = CMCTask p fid ctl st ks) &&
     (cm_capply p fid CMPutcK ctl st ks =
        CMCTask p fid ctl st ks) &&
     (cm_capply p fid CMPutiK ctl st ks =
        CMCTask p fid ctl st ks) &&
     (cm_capply p fid CMExitK ctl st ks =
        CMCTask p fid ctl st ks) &&
     (cm_capply p fid CMExprStmtK ctl st ks =
        CMCTask p fid ctl st ks) &&
     (!slot. cm_capply p fid (CMInitK (slot:int)) ctl st ks =
        CMCTask p fid ctl st ks) &&
     (!oldenv oldregions.
        cm_capply p fid
          (CMBlockK (oldenv:int->int->cm_value)
             (oldregions:(cm_region)list)) ctl st ks =
        CMCTask p fid ctl
          (cm_restore_scope st oldenv oldregions) ks) &&
     (!second.
        cm_capply p fid (CMSeqK (second:cm_stmt)) ctl st ks =
        (if cm_control_kind ctl == 0i
         then CMSTask p fid second st ks
         else CMCTask p fid ctl st ks)) &&
     (!yes no.
        cm_capply p fid
          (CMIfK (yes:cm_stmt) (no:cm_stmt)) ctl st ks =
        CMCTask p fid ctl st ks) &&
     (!guard body.
        cm_capply p fid
          (CMWhileGuardK (guard:cm_expr) (body:cm_stmt))
          ctl st ks = CMCTask p fid ctl st ks) &&
     (!guard body oldenv oldregions.
        cm_capply p fid
          (CMWhileBodyK (guard:cm_expr) (body:cm_stmt)
             (oldenv:int->int->cm_value)
             (oldregions:(cm_region)list)) ctl st ks =
        (if cm_control_kind ctl == 0i ||
            cm_control_kind ctl == 2i
         then CMRTask p fid guard
                (cm_restore_scope st oldenv oldregions)
                (CMWhileGuardK guard body :: ks)
         else if cm_control_kind ctl == 1i
              then CMCTask p fid CMNormal
                     (cm_restore_scope st oldenv oldregions) ks
              else CMCTask p fid ctl
                     (cm_restore_scope st oldenv oldregions) ks)) &&
     (cm_capply p fid CMReturnK ctl st ks =
        CMCTask p fid ctl st ks) &&
     (!callee rest values ret.
        cm_capply p fid
          (CMArgK (callee:int) (rest:(cm_expr)list)
             (values:(cm_value)list) (ret:cm_type))
          ctl st ks = CMCTask p fid ctl st ks) &&
     (!caller oldenv oldfp oldregions ret.
        cm_capply p fid
          (CMCallK (caller:int) (oldenv:int->int->cm_value)
             (oldfp:int) (oldregions:(cm_region)list)
             (ret:cm_type)) ctl st ks =
        (if cm_control_kind ctl == 3i
         then CMVTask p caller
                (cm_convert_value
                  (cm_restore_call st oldenv oldfp oldregions)
                  ret (cm_control_value ctl))
                (cm_restore_call st oldenv oldfp oldregions) ks
         else if cm_control_kind ctl == 0i
              then CMVTask p caller
                     (cm_convert_value
                       (cm_restore_call st oldenv oldfp oldregions)
                       ret (CMIntV 0i))
                     (cm_restore_call st oldenv oldfp oldregions) ks
              else CMCTask p caller ctl
                     (cm_restore_call st oldenv oldfp oldregions) ks))`);
PROOF int _e_cm_capply = cst_add_const_to_header(`cm_capply`);

PROOF thm cm_step_def = new_rec_definition(cm_task_RECURSION,
    `(cm_step (CMStartTask (p:cm_program) (input:(int)list)) =
        cm_begin_call p (--1i) (cm_program_main p) []
          (cm_initial_state p input) CMIntTy [CMHaltK]) &&
     (!p fid expr st ks.
        cm_step
          (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
             (st:cm_src_state) (ks:(cm_frame)list)) =
        cm_rstart p fid expr st ks) &&
     (!p fid expr st ks.
        cm_step
          (CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
             (st:cm_src_state) (ks:(cm_frame)list)) =
        cm_lstart p fid expr st ks) &&
     (!p fid stmt st ks.
        cm_step
          (CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
             (st:cm_src_state) (ks:(cm_frame)list)) =
        cm_sstart p fid stmt st ks) &&
     (!p fid v st ks.
        cm_step
          (CMVTask (p:cm_program) (fid:int) (v:cm_value)
             (st:cm_src_state) (ks:(cm_frame)list)) =
        (if ks == []
         then CMDoneTask st (CMError 2i) 2i
         else cm_vapply p fid (HD ks) v st (TL ks))) &&
     (!p fid ctl st ks.
        cm_step
          (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
             (st:cm_src_state) (ks:(cm_frame)list)) =
        (if cm_control_kind ctl == 4i
         then CMDoneTask st ctl (cm_control_status ctl)
         else if ks == []
         then if cm_control_kind ctl == 5i
              then CMDoneTask st ctl (cm_control_status ctl)
              else CMDoneTask st (CMError 2i) 2i
         else cm_capply p fid (HD ks) ctl st (TL ks))) &&
     (!st ctl status.
        cm_step
          (CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int)) =
        CMDoneTask st ctl status)`);
PROOF int _e_cm_step = cst_add_const_to_header(`cm_step`);

PROOF thm cm_task_done_def = new_rec_definition(cm_task_RECURSION,
    `(cm_task_done (CMStartTask (p:cm_program) (input:(int)list)) = F) &&
     (!p fid expr st ks.
        cm_task_done (CMRTask p fid expr st ks) = F) &&
     (!p fid expr st ks.
        cm_task_done (CMLTask p fid expr st ks) = F) &&
     (!p fid stmt st ks.
        cm_task_done (CMSTask p fid stmt st ks) = F) &&
     (!p fid v st ks.
        cm_task_done (CMVTask p fid v st ks) = F) &&
     (!p fid ctl st ks.
        cm_task_done (CMCTask p fid ctl st ks) = F) &&
     (!st ctl status.
        cm_task_done
          (CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int)) =
        T)`);
PROOF int _e_cm_task_done = cst_add_const_to_header(`cm_task_done`);

PROOF thm cm_task_outcome_def = new_rec_definition(cm_task_RECURSION,
    `(cm_task_outcome (CMStartTask (p:cm_program) (input:(int)list)) =
        CMOutcome (cm_initial_state p input) (CMError 2i) 2i) &&
     (!p fid expr st ks.
        cm_task_outcome (CMRTask p fid expr st ks) =
          CMOutcome st (CMError 2i) 2i) &&
     (!p fid expr st ks.
        cm_task_outcome (CMLTask p fid expr st ks) =
          CMOutcome st (CMError 2i) 2i) &&
     (!p fid stmt st ks.
        cm_task_outcome (CMSTask p fid stmt st ks) =
          CMOutcome st (CMError 2i) 2i) &&
     (!p fid v st ks.
        cm_task_outcome (CMVTask p fid v st ks) =
          CMOutcome st (CMError 2i) 2i) &&
     (!p fid ctl st ks.
        cm_task_outcome (CMCTask p fid ctl st ks) =
          CMOutcome st (CMError 2i) 2i) &&
     (!st ctl status.
        cm_task_outcome
          (CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int)) =
        CMOutcome st ctl status)`);
PROOF int _e_cm_task_outcome =
    cst_add_const_to_header(`cm_task_outcome`);

PROOF thm cm_iter_def = new_rec_definition(
    get_theorem_by_name("num_RECURSION"),
    `(cm_iter 0 (task:cm_task) = task) &&
     (!n task.
        cm_iter (SUC (n:num)) (task:cm_task) =
        cm_iter n (cm_step task))`);
PROOF int _e_cm_iter = cst_add_const_to_header(`cm_iter`);

/* Least big-step closure of the deterministic continuation machine. */
PROOF thm cm_exec_closed_def = new_fun_definition(
    `cm_exec_closed (P:cm_task->cm_outcome->bool) <=>
       (!st ctl status.
          P (CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int))
            (CMOutcome st ctl status)) &&
       (!task out.
          P (cm_step (task:cm_task)) (out:cm_outcome) ==>
          P task out)`);
PROOF int _e_cm_exec_closed =
    cst_add_const_to_header(`cm_exec_closed`);

PROOF thm cm_exec_def = new_fun_definition(
    `cm_exec (task:cm_task) (out:cm_outcome) <=>
       !P. cm_exec_closed P ==> P task out`);
PROOF int _e_cm_exec = cst_add_const_to_header(`cm_exec`);

PROOF static thm cm_exec_clause(const int index) {
  thm clauses = pure_rewrite_rule(THM_LIST(cm_exec_closed_def),
      assume_rule(`cm_exec_closed (P:cm_task->cm_outcome->bool)`));
  return index == 0 ? conjunct1_rule(clauses) : conjunct2_rule(clauses);
}

PROOF static thm cm_exec_use(const term app) {
  return mp_rule(spec_rule(`P:cm_task->cm_outcome->bool`,
      pure_rewrite_rule(THM_LIST(cm_exec_def), assume_rule(app))),
      assume_rule(`cm_exec_closed (P:cm_task->cm_outcome->bool)`));
}

PROOF static gnode cm_exec_goal(const gnode root) {
  gnode intro = AUTO_INTROS_TAC(root);
  gnode unfolded =
      CONV_TAC(intro, pure_rewrite_conv(THM_LIST(cm_exec_def)));
  return DISCH_TAC(GEN_TAC(unfolded, "P"), "Hclosed");
}

PROOF thm mk_cm_exec_done(void) {
  gnode root = gnode_new_with_ccl(
      `!st ctl status.
         cm_exec
           (CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int))
           (CMOutcome st ctl status)`);
  gnode leaf = cm_exec_goal(root);
  ACCEPT_TAC(leaf, specl_rule(
      TERM_LIST(`st:cm_src_state`, `ctl:cm_control`, `status:int`),
      cm_exec_clause(0)));
  return gnode_prove(root);
}
PROOF thm cm_exec_done = mk_cm_exec_done();

PROOF thm mk_cm_exec_rule(void) {
  gnode root = gnode_new_with_ccl(
      `!task out. cm_exec (cm_step (task:cm_task)) (out:cm_outcome) ==>
         cm_exec task out`);
  gnode leaf = cm_exec_goal(root);
  thm clause = specl_rule(TERM_LIST(`task:cm_task`, `out:cm_outcome`),
      cm_exec_clause(1));
  ACCEPT_TAC(leaf, mp_rule(clause,
      cm_exec_use(`cm_exec (cm_step (task:cm_task)) (out:cm_outcome)`)));
  return gnode_prove(root);
}
PROOF thm cm_exec_rule = mk_cm_exec_rule();

PROOF thm mk_cm_exec_induct(void) {
  gnode root = gnode_new_with_ccl(
      `!P. cm_exec_closed P ==>
        (!task out. cm_exec task out ==>
          P (task:cm_task) (out:cm_outcome))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  ACCEPT_TAC(leaf, cm_exec_use(
      `cm_exec (task:cm_task) (out:cm_outcome)`));
  return gnode_prove(root);
}
PROOF thm cm_exec_induct = mk_cm_exec_induct();

PROOF thm cm_reaches_def = new_fun_definition(
    `cm_reaches (task:cm_task) (out:cm_outcome) : bool =
       (?n st ctl status.
          cm_iter n task ==
            CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int) &&
          out == CMOutcome st ctl status)`);
PROOF int _e_cm_reaches = cst_add_const_to_header(`cm_reaches`);

PROOF thm mk_cm_reaches_closed(void) {
  gnode root = gnode_new_with_ccl(
      `cm_exec_closed (cm_reaches:cm_task->cm_outcome->bool)`);
  gnode leaf =
      CONV_TAC(root, pure_rewrite_conv(THM_LIST(cm_exec_closed_def)));
  gnode_list parts = CONJ_TAC(leaf);
  {
    gnode done = AUTO_INTROS_TAC(parts[0]);
    gnode tgt = CONV_TAC(done,
        pure_rewrite_conv(THM_LIST(cm_reaches_def)));
    thm iter0 = inst_rule(TERM_PAIR_LIST(
        (term_pair){
          `CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int)`,
          `task:cm_task`}), conjunct1_rule(cm_iter_def));
    thm body = conj_rule(iter0,
        refl_rule(
          `CMOutcome (st:cm_src_state) (ctl:cm_control) (status:int)`));
    thm exs = exists_rule(
        `?n st0 ctl0 status0.
           cm_iter n
             (CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int)) ==
             CMDoneTask (st0:cm_src_state) (ctl0:cm_control) (status0:int) &&
           CMOutcome st ctl status == CMOutcome st0 ctl0 status0`,
        `0:num`, exists_rule(
          `?st0 ctl0 status0.
             cm_iter 0
               (CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int)) ==
               CMDoneTask (st0:cm_src_state) (ctl0:cm_control) (status0:int) &&
             CMOutcome st ctl status == CMOutcome st0 ctl0 status0`,
          `st:cm_src_state`, exists_rule(
            `?ctl0 status0.
               cm_iter 0
                 (CMDoneTask (st:cm_src_state)
                   (ctl:cm_control) (status:int)) ==
                 CMDoneTask (st:cm_src_state)
                   (ctl0:cm_control) (status0:int) &&
               CMOutcome st ctl status == CMOutcome st ctl0 status0`,
            `ctl:cm_control`, exists_rule(
              `?status0.
                 cm_iter 0
                   (CMDoneTask (st:cm_src_state)
                     (ctl:cm_control) (status:int)) ==
                   CMDoneTask (st:cm_src_state)
                     (ctl:cm_control) (status0:int) &&
                 CMOutcome st ctl status == CMOutcome st ctl status0`,
              `status:int`, body))));
    ACCEPT_TAC(tgt, exs);
  }
  {
    gnode step = AUTO_INTROS_TAC(parts[1]);
    thm reach = pure_rewrite_rule(THM_LIST(cm_reaches_def),
        assume_rule(`cm_reaches (cm_step (task:cm_task))
          (out:cm_outcome)`));
    thm body0 = assume_rule(
        `cm_iter (n:num) (cm_step (task:cm_task)) ==
           CMDoneTask (st0:cm_src_state)
             (ctl0:cm_control) (status0:int) &&
         (out:cm_outcome) == CMOutcome st0 ctl0 status0`);
    thm iter_suc = specl_rule(TERM_LIST(`n:num`, `task:cm_task`),
        conjunct2_rule(cm_iter_def));
    thm advanced = trans_rule(iter_suc, conjunct1_rule(body0));
    thm body = conj_rule(advanced, conjunct2_rule(body0));
    thm exs = exists_rule(
        `?m st1 ctl1 status1.
           cm_iter m (task:cm_task) ==
             CMDoneTask (st1:cm_src_state)
               (ctl1:cm_control) (status1:int) &&
           (out:cm_outcome) == CMOutcome st1 ctl1 status1`,
        `SUC (n:num)`, exists_rule(
          `?st1 ctl1 status1.
             cm_iter (SUC (n:num)) (task:cm_task) ==
               CMDoneTask (st1:cm_src_state)
                 (ctl1:cm_control) (status1:int) &&
             (out:cm_outcome) == CMOutcome st1 ctl1 status1`,
          `st0:cm_src_state`, exists_rule(
            `?ctl1 status1.
               cm_iter (SUC (n:num)) (task:cm_task) ==
                 CMDoneTask (st0:cm_src_state)
                   (ctl1:cm_control) (status1:int) &&
               (out:cm_outcome) == CMOutcome st0 ctl1 status1`,
            `ctl0:cm_control`, exists_rule(
              `?status1.
                 cm_iter (SUC (n:num)) (task:cm_task) ==
                   CMDoneTask (st0:cm_src_state)
                     (ctl0:cm_control) (status1:int) &&
                 (out:cm_outcome) == CMOutcome st0 ctl0 status1`,
              `status0:int`, body))));
    thm no_status = choose_rule(`status0:int`,
        assume_rule(
          `?status0.
             cm_iter (n:num) (cm_step (task:cm_task)) ==
               CMDoneTask (st0:cm_src_state)
                 (ctl0:cm_control) (status0:int) &&
             (out:cm_outcome) == CMOutcome st0 ctl0 status0`), exs);
    thm no_control = choose_rule(`ctl0:cm_control`,
        assume_rule(
          `?ctl0 status0.
             cm_iter (n:num) (cm_step (task:cm_task)) ==
               CMDoneTask (st0:cm_src_state)
                 (ctl0:cm_control) (status0:int) &&
             (out:cm_outcome) == CMOutcome st0 ctl0 status0`), no_status);
    thm no_state = choose_rule(`st0:cm_src_state`,
        assume_rule(
          `?st0 ctl0 status0.
             cm_iter (n:num) (cm_step (task:cm_task)) ==
               CMDoneTask (st0:cm_src_state)
                 (ctl0:cm_control) (status0:int) &&
             (out:cm_outcome) == CMOutcome st0 ctl0 status0`), no_control);
    thm result = choose_rule(`n:num`, reach, no_state);
    gnode tgt = CONV_TAC(step,
        pure_rewrite_conv(THM_LIST(cm_reaches_def)));
    ACCEPT_TAC(tgt, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_reaches_closed = mk_cm_reaches_closed();

PROOF thm mk_cm_exec_reaches(void) {
  thm body = mp_rule(spec_rule(
      `cm_reaches:cm_task->cm_outcome->bool`,
      pure_rewrite_rule(THM_LIST(cm_exec_def),
        assume_rule(`cm_exec (task:cm_task) (out:cm_outcome)`))),
      cm_reaches_closed);
  return close_implication(
      `!task out. cm_exec (task:cm_task) (out:cm_outcome) ==>
         cm_reaches task out`, body);
}
PROOF thm cm_exec_reaches = mk_cm_exec_reaches();

PROOF static thm mk_cm_exec_witness(void) {
  return conv_rule(rewrite_conv(THM_LIST(cm_reaches_def)),
      cm_exec_reaches);
}
PROOF static thm cm_exec_witness = mk_cm_exec_witness();
PROOF thm get_cm_exec_witness(void) {
  return cm_exec_witness;
}

PROOF thm mk_cm_done_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(task:cm_task). cm_task_done task ==> cm_step task == task`);
  gnode_list cases = INDUCT_TAC(root, `task:cm_task`);
  for (size_t i = 0; i < 6; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    thm impossible = conv_rule(reduce_rewrite_conv(
        THM_LIST(cm_task_done_def)),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    CONTR_TAC(leaf, impossible);
  }
  gnode done = AUTO_INTROS_TAC(cases[6]);
  CONV_TAC(done, reduce_rewrite_conv(
      THM_LIST(cm_task_done_def, cm_step_def)));
  return gnode_prove(root);
}
PROOF thm cm_done_step = mk_cm_done_step();
PROOF thm get_cm_done_step(void) {
  return cm_done_step;
}

PROOF thm mk_cm_done_iter(void) {
  gnode root = gnode_new_with_ccl(
      `!(n:num) (task:cm_task). cm_task_done task ==>
         cm_iter n task == task`);
  gnode_list cases = INDUCT_TAC(root, `n:num`);
  {
    gnode base = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(base, rewrite_conv(THM_LIST(cm_iter_def)));
  }
  {
    gnode step = AUTO_INTROS_TAC(cases[1]);
    thm ih = mp_rule(spec_rule(`task:cm_task`,
        assume_rule(goal_lasmps(step->g)[0].tm)),
        assume_rule(goal_lasmps(step->g)[1].tm));
    thm fixed = mp_rule(spec_rule(`task:cm_task`, cm_done_step),
        assume_rule(goal_lasmps(step->g)[1].tm));
    thm unfolded = specl_rule(TERM_LIST(`n:num`, `task:cm_task`),
        conjunct2_rule(cm_iter_def));
    thm congr = ap_term_rule(`cm_iter (n:num)`,
        fixed);
    ACCEPT_TAC(step, trans_rule(unfolded,
        trans_rule(congr, ih)));
  }
  return gnode_prove(root);
}
PROOF thm cm_done_iter = mk_cm_done_iter();

PROOF thm mk_cm_done_outcome_unique(void) {
  gnode root = gnode_new_with_ccl(
      `!(n:num). !(m:num) (task:cm_task).
         cm_task_done (cm_iter n task) &&
         cm_task_done (cm_iter m task) ==>
         cm_task_outcome (cm_iter n task) ==
         cm_task_outcome (cm_iter m task)`);
  gnode_list ncases = INDUCT_TAC(root, `n:num`);
  {
    gnode base = AUTO_INTROS_TAC(ncases[0]);
    thm both = assume_rule(goal_lasmps(base->g)[0].tm);
    thm done = conv_rule(rewrite_conv(THM_LIST(cm_iter_def)),
        conjunct1_rule(both));
    thm fixed = mp_rule(specl_rule(TERM_LIST(`m:num`, `task:cm_task`),
        cm_done_iter), done);
    thm left = ap_term_rule(`cm_task_outcome`,
        inst_rule(TERM_PAIR_LIST(
          (term_pair){`task:cm_task`, `task:cm_task`}),
          conjunct1_rule(cm_iter_def)));
    thm right = ap_term_rule(`cm_task_outcome`, fixed);
    ACCEPT_TAC(base, trans_rule(left, sym_rule(right)));
  }
  gnode_list mcases = INDUCT_TAC(ncases[1], `m:num`);
  {
    gnode base = AUTO_INTROS_TAC(mcases[0]);
    thm both = assume_rule(goal_lasmps(base->g)[1].tm);
    thm done = conv_rule(rewrite_conv(THM_LIST(cm_iter_def)),
        conjunct2_rule(both));
    thm fixed = mp_rule(specl_rule(
        TERM_LIST(`SUC (n:num)`, `task:cm_task`), cm_done_iter), done);
    thm left = ap_term_rule(`cm_task_outcome`, fixed);
    thm right = ap_term_rule(`cm_task_outcome`,
        inst_rule(TERM_PAIR_LIST(
          (term_pair){`task:cm_task`, `task:cm_task`}),
          conjunct1_rule(cm_iter_def)));
    ACCEPT_TAC(base, trans_rule(left, sym_rule(right)));
  }
  {
    gnode step = AUTO_INTROS_TAC(mcases[1]);
    thm both = assume_rule(goal_lasmps(step->g)[2].tm);
    thm left_done = conv_rule(rewrite_conv(THM_LIST(cm_iter_def)),
        conjunct1_rule(both));
    thm right_done = conv_rule(rewrite_conv(THM_LIST(cm_iter_def)),
        conjunct2_rule(both));
    thm ih = specl_rule(TERM_LIST(`n_:num`,
        `cm_step (task:cm_task)`),
        assume_rule(goal_lasmps(step->g)[0].tm));
    thm same = mp_rule(ih, conj_rule(left_done, right_done));
    gnode tgt = CONV_TAC(step, rewrite_conv(THM_LIST(cm_iter_def)));
    ACCEPT_TAC(tgt, same);
  }
  return gnode_prove(root);
}
PROOF thm cm_done_outcome_unique = mk_cm_done_outcome_unique();

PROOF thm mk_cm_reaches_witness(void) {
  thm reach = pure_rewrite_rule(THM_LIST(cm_reaches_def),
      assume_rule(`cm_reaches (task:cm_task) (out:cm_outcome)`));
  thm body0 = assume_rule(
      `cm_iter (n:num) (task:cm_task) ==
         CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int) &&
       (out:cm_outcome) == CMOutcome st ctl status`);
  thm iter_eq = conjunct1_rule(body0);
  thm done = conv_rule(reduce_rewrite_conv(
      THM_LIST(cm_task_done_def)),
      ap_term_rule(`cm_task_done`, iter_eq));
  thm iter_out = conv_rule(reduce_rewrite_conv(
      THM_LIST(cm_task_outcome_def)),
      ap_term_rule(`cm_task_outcome`, iter_eq));
  thm out_eq = trans_rule(conjunct2_rule(body0), sym_rule(iter_out));
  thm exs = exists_rule(
      `?m. cm_task_done (cm_iter m (task:cm_task)) &&
           (out:cm_outcome) == cm_task_outcome (cm_iter m task)`,
      `n:num`, conj_rule(done, out_eq));
  thm no_status = choose_rule(`status:int`,
      assume_rule(
        `?status.
           cm_iter (n:num) (task:cm_task) ==
             CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int) &&
           (out:cm_outcome) == CMOutcome st ctl status`), exs);
  thm no_control = choose_rule(`ctl:cm_control`,
      assume_rule(
        `?ctl status.
           cm_iter (n:num) (task:cm_task) ==
             CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int) &&
           (out:cm_outcome) == CMOutcome st ctl status`), no_status);
  thm no_state = choose_rule(`st:cm_src_state`,
      assume_rule(
        `?st ctl status.
           cm_iter (n:num) (task:cm_task) ==
             CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int) &&
           (out:cm_outcome) == CMOutcome st ctl status`), no_control);
  thm result = choose_rule(`n:num`, reach, no_state);
  return close_implication(
      `!task out. cm_reaches (task:cm_task) (out:cm_outcome) ==>
         ?n. cm_task_done (cm_iter n task) &&
             out == cm_task_outcome (cm_iter n task)`, result);
}
PROOF thm cm_reaches_witness = mk_cm_reaches_witness();

PROOF thm mk_cm_reaches_unique(void) {
  thm h1 = assume_rule(
      `cm_reaches (task:cm_task) (out1:cm_outcome)`);
  thm h2 = assume_rule(
      `cm_reaches (task:cm_task) (out2:cm_outcome)`);
  thm ex1 = mp_rule(specl_rule(
      TERM_LIST(`task:cm_task`, `out1:cm_outcome`),
      cm_reaches_witness), h1);
  thm ex2 = mp_rule(specl_rule(
      TERM_LIST(`task:cm_task`, `out2:cm_outcome`),
      cm_reaches_witness), h2);
  thm b1 = assume_rule(
      `cm_task_done (cm_iter (n:num) (task:cm_task)) &&
       (out1:cm_outcome) == cm_task_outcome (cm_iter n task)`);
  thm b2 = assume_rule(
      `cm_task_done (cm_iter (m:num) (task:cm_task)) &&
       (out2:cm_outcome) == cm_task_outcome (cm_iter m task)`);
  thm same = mp_rule(specl_rule(
      TERM_LIST(`n:num`, `m:num`, `task:cm_task`),
      cm_done_outcome_unique),
      conj_rule(conjunct1_rule(b1), conjunct1_rule(b2)));
  thm result0 = trans_rule(conjunct2_rule(b1),
      trans_rule(same, sym_rule(conjunct2_rule(b2))));
  thm result1 = choose_rule(`m:num`, ex2, result0);
  thm result = choose_rule(`n:num`, ex1, result1);
  return close_implication(
      `!task out1 out2.
         cm_reaches (task:cm_task) (out1:cm_outcome) ==>
         cm_reaches task (out2:cm_outcome) ==> out1 == out2`, result);
}
PROOF thm cm_reaches_unique = mk_cm_reaches_unique();

PROOF thm mk_cm_exec_deterministic(void) {
  thm e1 = assume_rule(`cm_exec (task:cm_task) (out1:cm_outcome)`);
  thm e2 = assume_rule(`cm_exec (task:cm_task) (out2:cm_outcome)`);
  thm r1 = mp_rule(specl_rule(
      TERM_LIST(`task:cm_task`, `out1:cm_outcome`),
      cm_exec_reaches), e1);
  thm r2 = mp_rule(specl_rule(
      TERM_LIST(`task:cm_task`, `out2:cm_outcome`),
      cm_exec_reaches), e2);
  thm result = mp_rule(mp_rule(specl_rule(
      TERM_LIST(`task:cm_task`, `out1:cm_outcome`, `out2:cm_outcome`),
      cm_reaches_unique), r1), r2);
  return close_implication(
      `!task out1 out2.
         cm_exec (task:cm_task) (out1:cm_outcome) ==>
         cm_exec task (out2:cm_outcome) ==> out1 == out2`, result);
}
PROOF thm cm_exec_deterministic = mk_cm_exec_deterministic();

PROOF thm mk_cm_terminal_exec(void) {
  gnode root = gnode_new_with_ccl(
      `!(task:cm_task). cm_task_done task ==>
         cm_exec task (cm_task_outcome task)`);
  gnode_list cases = INDUCT_TAC(root, `task:cm_task`);
  for (size_t i = 0; i < 6; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    thm impossible = conv_rule(reduce_rewrite_conv(
        THM_LIST(cm_task_done_def)),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    CONTR_TAC(leaf, impossible);
  }
  gnode done = AUTO_INTROS_TAC(cases[6]);
  CONV_TAC(done, reduce_rewrite_conv(
      THM_LIST(cm_task_done_def, cm_task_outcome_def, cm_exec_done)));
  return gnode_prove(root);
}
PROOF thm cm_terminal_exec = mk_cm_terminal_exec();

PROOF thm mk_cm_done_iter_exec(void) {
  gnode root = gnode_new_with_ccl(
      `!(n:num). !(task:cm_task).
         cm_task_done (cm_iter n task) ==>
         cm_exec task (cm_task_outcome (cm_iter n task))`);
  gnode_list cases = INDUCT_TAC(root, `n:num`);
  {
    gnode base = AUTO_INTROS_TAC(cases[0]);
    thm done = conv_rule(rewrite_conv(THM_LIST(cm_iter_def)),
        assume_rule(goal_lasmps(base->g)[0].tm));
    thm run = mp_rule(spec_rule(`task:cm_task`, cm_terminal_exec), done);
    gnode tgt = CONV_TAC(base, rewrite_conv(THM_LIST(cm_iter_def)));
    ACCEPT_TAC(tgt, run);
  }
  {
    gnode step = AUTO_INTROS_TAC(cases[1]);
    thm done = conv_rule(rewrite_conv(THM_LIST(cm_iter_def)),
        assume_rule(goal_lasmps(step->g)[1].tm));
    thm tail = mp_rule(spec_rule(`cm_step (task:cm_task)`,
        assume_rule(goal_lasmps(step->g)[0].tm)), done);
    thm run = mp_rule(specl_rule(
        TERM_LIST(`task:cm_task`,
          `cm_task_outcome (cm_iter (n:num) (cm_step task))`),
        cm_exec_rule), tail);
    gnode tgt = CONV_TAC(step, rewrite_conv(THM_LIST(cm_iter_def)));
    ACCEPT_TAC(tgt, run);
  }
  return gnode_prove(root);
}
PROOF thm cm_done_iter_exec = mk_cm_done_iter_exec();

PROOF thm mk_cm_witness_exec(void) {
  thm both = assume_rule(
      `cm_task_done (cm_iter (n:num) (task:cm_task)) &&
       (out:cm_outcome) == cm_task_outcome (cm_iter n task)`);
  thm run = mp_rule(specl_rule(
      TERM_LIST(`n:num`, `task:cm_task`), cm_done_iter_exec),
      conjunct1_rule(both));
  thm replace = beta_norm(ap_term_rule(
      `\result:cm_outcome. cm_exec (task:cm_task) result`,
      sym_rule(conjunct2_rule(both))));
  thm result = eq_mp_rule(replace, run);
  return close_implication(
      `!n task out.
         cm_task_done (cm_iter (n:num) (task:cm_task)) &&
         (out:cm_outcome) == cm_task_outcome (cm_iter n task) ==>
         cm_exec task out`, result);
}
PROOF thm cm_witness_exec = mk_cm_witness_exec();

PROOF thm mk_cm_witness_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(n:num). !task out.
         ~(cm_task_done (task:cm_task)) ==>
         cm_task_done (cm_iter n task) &&
         (out:cm_outcome) == cm_task_outcome (cm_iter n task) ==>
         cm_exec (cm_step task) out`);
  gnode_list cases = INDUCT_TAC(root, `n:num`);
  {
    gnode base = AUTO_INTROS_TAC(cases[0]);
    thm not_done = assume_rule(goal_lasmps(base->g)[0].tm);
    thm both = assume_rule(goal_lasmps(base->g)[1].tm);
    thm done = conv_rule(rewrite_conv(THM_LIST(cm_iter_def)),
        conjunct1_rule(both));
    CONTR_TAC(base, contra(not_done, done));
  }
  {
    gnode step = AUTO_INTROS_TAC(cases[1]);
    thm both = assume_rule(goal_lasmps(step->g)[2].tm);
    thm done = conv_rule(rewrite_conv(THM_LIST(cm_iter_def)),
        conjunct1_rule(both));
    thm out_eq = conv_rule(rewrite_conv(THM_LIST(cm_iter_def)),
        conjunct2_rule(both));
    thm run = mp_rule(specl_rule(TERM_LIST(`n:num`,
        `cm_step (task:cm_task)`, `out:cm_outcome`),
        cm_witness_exec), conj_rule(done, out_eq));
    ACCEPT_TAC(step, run);
  }
  return gnode_prove(root);
}
PROOF thm cm_witness_step = mk_cm_witness_step();

PROOF thm mk_cm_exec_step_inv(void) {
  thm not_done = assume_rule(`~(cm_task_done (task:cm_task))`);
  thm run = assume_rule(`cm_exec (task:cm_task) (out:cm_outcome)`);
  thm reach = mp_rule(specl_rule(
      TERM_LIST(`task:cm_task`, `out:cm_outcome`),
      cm_exec_reaches), run);
  thm witness = mp_rule(specl_rule(
      TERM_LIST(`task:cm_task`, `out:cm_outcome`),
      cm_reaches_witness), reach);
  thm body = assume_rule(
      `cm_task_done (cm_iter (n:num) (task:cm_task)) &&
       (out:cm_outcome) == cm_task_outcome (cm_iter n task)`);
  thm stepped = mp_rule(mp_rule(specl_rule(
      TERM_LIST(`n:num`, `task:cm_task`, `out:cm_outcome`),
      cm_witness_step), not_done), body);
  thm result = choose_rule(`n:num`, witness, stepped);
  return close_implication(
      `!task out. ~(cm_task_done (task:cm_task)) ==>
         cm_exec task (out:cm_outcome) ==> cm_exec (cm_step task) out`,
      result);
}
PROOF thm cm_exec_step_inv = mk_cm_exec_step_inv();

PROOF thm mk_cm_exec_skip(void) {
  thm after = assume_rule(
      `cm_exec
         (CMCTask (p:cm_program) (fid:int) CMNormal
           (st:cm_src_state) (ks:(cm_frame)list))
         (out:cm_outcome)`);
  thm step_eq = apply_conversion(reduce_rewrite_conv(
      THM_LIST(cm_step_def, cm_sstart_def)),
      `cm_step
         (CMSTask (p:cm_program) (fid:int) CMSkipS
           (st:cm_src_state) (ks:(cm_frame)list))`);
  thm lifted = beta_norm(ap_term_rule(
      `\next:cm_task. cm_exec next (out:cm_outcome)`, step_eq));
  thm premise = eq_mp_rule(sym_rule(lifted), after);
  thm result = mp_rule(specl_rule(TERM_LIST(
      `CMSTask (p:cm_program) (fid:int) CMSkipS
        (st:cm_src_state) (ks:(cm_frame)list)`,
      `out:cm_outcome`), cm_exec_rule), premise);
  return close_implication(
      `!p fid st ks out.
         cm_exec
           (CMCTask (p:cm_program) (fid:int) CMNormal
             (st:cm_src_state) (ks:(cm_frame)list))
           (out:cm_outcome) ==>
         cm_exec (CMSTask p fid CMSkipS st ks) out`, result);
}
PROOF thm cm_exec_skip = mk_cm_exec_skip();

PROOF thm mk_cm_exec_const(void) {
  thm after = assume_rule(
      `cm_exec
         (CMVTask (p:cm_program) (fid:int)
           (CMIntV (tower_wrap64 (n:int)))
           (st:cm_src_state) (ks:(cm_frame)list))
         (out:cm_outcome)`);
  thm step_eq = apply_conversion(reduce_rewrite_conv(
      THM_LIST(cm_step_def, cm_rstart_def,
        cm_convert_value_def, cm_value_number_def,
        get_tower_wrap64_idempotent())),
      `cm_step
         (CMRTask (p:cm_program) (fid:int)
           (CMConstE (n:int) CMIntTy)
           (st:cm_src_state) (ks:(cm_frame)list))`);
  thm lifted = beta_norm(ap_term_rule(
      `\next:cm_task. cm_exec next (out:cm_outcome)`, step_eq));
  thm premise = eq_mp_rule(sym_rule(lifted), after);
  thm result = mp_rule(specl_rule(TERM_LIST(
      `CMRTask (p:cm_program) (fid:int)
        (CMConstE (n:int) CMIntTy)
        (st:cm_src_state) (ks:(cm_frame)list)`,
      `out:cm_outcome`), cm_exec_rule), premise);
  return close_implication(
      `!p fid n st ks out.
         cm_exec
           (CMVTask (p:cm_program) (fid:int)
             (CMIntV (tower_wrap64 (n:int)))
             (st:cm_src_state) (ks:(cm_frame)list))
           (out:cm_outcome) ==>
         cm_exec
           (CMRTask p fid (CMConstE n CMIntTy) st ks) out`, result);
}
PROOF thm cm_exec_const = mk_cm_exec_const();

PROOF thm mk_cm_exec_skip_inv(void) {
  term start =
      `CMSTask (p:cm_program) (fid:int) CMSkipS
        (st:cm_src_state) (ks:(cm_frame)list)`;
  thm impossible = conv_rule(reduce_rewrite_conv(
      THM_LIST(cm_task_done_def)),
      assume_rule(mk_comb(`cm_task_done`, start)));
  thm not_done = not_intro(mk_comb(`cm_task_done`, start), impossible);
  thm stepped = mp_rule(mp_rule(specl_rule(TERM_LIST(
      start, `out:cm_outcome`), cm_exec_step_inv), not_done),
      assume_rule(mk_comb(mk_comb(`cm_exec`, start),
        `out:cm_outcome`)));
  thm step_eq = apply_conversion(reduce_rewrite_conv(
      THM_LIST(cm_step_def, cm_sstart_def)),
      mk_comb(`cm_step`, start));
  thm lifted = beta_norm(ap_term_rule(
      `\next:cm_task. cm_exec next (out:cm_outcome)`, step_eq));
  thm result = eq_mp_rule(lifted, stepped);
  return close_implication(
      `!p fid st ks out.
         cm_exec
           (CMSTask (p:cm_program) (fid:int) CMSkipS
             (st:cm_src_state) (ks:(cm_frame)list))
           (out:cm_outcome) ==>
         cm_exec (CMCTask p fid CMNormal st ks) out`, result);
}
PROOF thm cm_exec_skip_inv = mk_cm_exec_skip_inv();

PROOF thm mk_cm_exec_const_inv(void) {
  term start =
      `CMRTask (p:cm_program) (fid:int)
        (CMConstE (n:int) CMIntTy)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  thm impossible = conv_rule(reduce_rewrite_conv(
      THM_LIST(cm_task_done_def)),
      assume_rule(mk_comb(`cm_task_done`, start)));
  thm not_done = not_intro(mk_comb(`cm_task_done`, start), impossible);
  thm stepped = mp_rule(mp_rule(specl_rule(TERM_LIST(
      start, `out:cm_outcome`), cm_exec_step_inv), not_done),
      assume_rule(mk_comb(mk_comb(`cm_exec`, start),
        `out:cm_outcome`)));
  thm step_eq = apply_conversion(reduce_rewrite_conv(
      THM_LIST(cm_step_def, cm_rstart_def,
        cm_convert_value_def, cm_value_number_def,
        get_tower_wrap64_idempotent())),
      mk_comb(`cm_step`, start));
  thm lifted = beta_norm(ap_term_rule(
      `\next:cm_task. cm_exec next (out:cm_outcome)`, step_eq));
  thm result = eq_mp_rule(lifted, stepped);
  return close_implication(
      `!p fid n st ks out.
         cm_exec
           (CMRTask (p:cm_program) (fid:int)
             (CMConstE (n:int) CMIntTy)
             (st:cm_src_state) (ks:(cm_frame)list))
           (out:cm_outcome) ==>
         cm_exec
           (CMVTask p fid (CMIntV (tower_wrap64 n)) st ks) out`, result);
}
PROOF thm cm_exec_const_inv = mk_cm_exec_const_inv();

PROOF thm cm_outcome_state_def =
  new_rec_definition(cm_outcome_RECURSION,
    `cm_outcome_state
       (CMOutcome (st:cm_src_state) (ctl:cm_control) (status:int)) = st`);
PROOF thm cm_outcome_control_def =
  new_rec_definition(cm_outcome_RECURSION,
    `cm_outcome_control
       (CMOutcome (st:cm_src_state) (ctl:cm_control) (status:int)) = ctl`);
PROOF thm cm_outcome_status_def =
  new_rec_definition(cm_outcome_RECURSION,
    `cm_outcome_status
       (CMOutcome (st:cm_src_state) (ctl:cm_control) (status:int)) =
       status`);
PROOF int _e_cm_outcome_state =
    cst_add_const_to_header(`cm_outcome_state`);
PROOF int _e_cm_outcome_control =
    cst_add_const_to_header(`cm_outcome_control`);
PROOF int _e_cm_outcome_status =
    cst_add_const_to_header(`cm_outcome_status`);

PROOF thm cm_valid_input_def = new_fun_definition(
    `cm_valid_input (input:(int)list) : bool =
       ALL (\byte:int. tower_byte_value byte) input`);
PROOF thm cm_success_control_def = new_fun_definition(
    `cm_success_control (ctl:cm_control) : bool =
       (cm_control_kind ctl == 3i || cm_control_kind ctl == 4i)`);
PROOF int _e_cm_valid_input =
    cst_add_const_to_header(`cm_valid_input`);
PROOF int _e_cm_success_control =
    cst_add_const_to_header(`cm_success_control`);

PROOF thm cm_source_safe_def = new_fun_definition(
    `cm_source_safe (p:cm_program) (input:(int)list) : bool =
       (cm_typed_program p && cm_valid_input input &&
        (?out. cm_exec (CMStartTask p input) (out:cm_outcome)) &&
        (!st ctl status.
           cm_exec (CMStartTask p input)
             (CMOutcome (st:cm_src_state)
               (ctl:cm_control) (status:int)) ==>
           cm_success_control ctl))`);
PROOF int _e_cm_source_safe =
    cst_add_const_to_header(`cm_source_safe`);

PROOF thm cm_source_terminates_def = new_fun_definition(
    `cm_source_terminates (p:cm_program) (input:(int)list)
       (output:(int)list) (status:int) : bool =
       (cm_valid_input input && tower_byte_value status &&
        ?st ctl.
          cm_exec (CMStartTask p input)
            (CMOutcome (st:cm_src_state) (ctl:cm_control) status) &&
          cm_success_control ctl &&
          cm_state_output st == output)`);
PROOF int _e_cm_source_terminates =
    cst_add_const_to_header(`cm_source_terminates`);

PROOF thm get_cm_source_safe_def(void) { return cm_source_safe_def; }
PROOF thm get_cm_exec_closed_def(void) { return cm_exec_closed_def; }
PROOF thm get_cm_exec_def(void) { return cm_exec_def; }
PROOF thm get_cm_exec_done(void) { return cm_exec_done; }
PROOF thm get_cm_exec_rule(void) { return cm_exec_rule; }
PROOF thm get_cm_exec_induct(void) { return cm_exec_induct; }
PROOF thm get_cm_exec_deterministic(void) {
  return cm_exec_deterministic;
}
PROOF thm get_cm_exec_step_inv(void) { return cm_exec_step_inv; }
PROOF thm get_cm_exec_skip(void) { return cm_exec_skip; }
PROOF thm get_cm_exec_const(void) { return cm_exec_const; }
PROOF thm get_cm_exec_skip_inv(void) { return cm_exec_skip_inv; }
PROOF thm get_cm_exec_const_inv(void) { return cm_exec_const_inv; }
PROOF thm get_cm_valid_input_def(void) {
  return cm_valid_input_def;
}
PROOF thm get_cm_source_terminates_def(void) {
  return cm_source_terminates_def;
}
PROOF thm get_cm_done_iter_exec(void) { return cm_done_iter_exec; }
PROOF thm get_cm_iter_def(void) { return cm_iter_def; }
PROOF thm get_cm_value_number_def(void) {
  return cm_value_number_def;
}
PROOF thm get_cm_pointer_retype_def(void) {
  return cm_pointer_retype_def;
}
PROOF thm get_cm_convert_value_def(void) {
  return cm_convert_value_def;
}
PROOF thm get_cm_is_pointer_def(void) {
  return cm_is_pointer_def;
}
PROOF thm get_cm_pointee_def(void) {
  return cm_pointee_def;
}
PROOF thm get_cm_value_type_def(void) {
  return cm_value_type_def;
}
PROOF thm get_cm_truth_def(void) { return cm_truth_def; }
PROOF thm get_cm_binary_ok_def(void) { return cm_binary_ok_def; }
PROOF thm get_cm_binary_value_def(void) { return cm_binary_value_def; }
PROOF thm get_cm_unary_value_def(void) { return cm_unary_value_def; }
PROOF thm get_cm_ptr_add_def(void) { return cm_ptr_add_def; }
PROOF thm get_cm_ptr_member_def(void) { return cm_ptr_member_def; }
PROOF thm get_cm_member_slot_def(void) { return cm_member_slot_def; }
PROOF thm get_cm_ptr_member_ok_def(void) {
  return cm_ptr_member_ok_def;
}
PROOF thm get_cm_global_pointer_def(void) {
  return cm_global_pointer_def;
}
PROOF thm get_cm_string_pointer_def(void) {
  return cm_string_pointer_def;
}
PROOF thm get_cm_global_generation_def(void) {
  return cm_global_generation_def;
}
PROOF thm get_cm_string_generation_def(void) {
  return cm_string_generation_def;
}
PROOF thm get_cm_first_dynamic_generation_def(void) {
  return cm_first_dynamic_generation_def;
}
PROOF thm get_cm_ptr_offset_def(void) { return cm_ptr_offset_def; }
PROOF thm get_cm_ptr_gen_def(void) { return cm_ptr_gen_def; }
PROOF thm get_cm_ptr_lo_def(void) { return cm_ptr_lo_def; }
PROOF thm get_cm_ptr_hi_def(void) { return cm_ptr_hi_def; }
PROOF thm get_cm_ptr_view_def(void) { return cm_ptr_view_def; }
PROOF thm get_cm_pointer_live_def(void) { return cm_pointer_live_def; }
PROOF thm get_cm_pointer_region_ok_def(void) {
  return cm_pointer_region_ok_def;
}
PROOF thm get_cm_pointer_writable_def(void) {
  return cm_pointer_writable_def;
}
PROOF thm get_cm_pointer_compatible_def(void) {
  return cm_pointer_compatible_def;
}
PROOF thm get_cm_is_null_value_def(void) {
  return cm_is_null_value_def;
}
PROOF thm get_cm_ptr_shift_ok_def(void) {
  return cm_ptr_shift_ok_def;
}
PROOF thm get_cm_ptr_diff_ok_def(void) {
  return cm_ptr_diff_ok_def;
}
PROOF thm get_cm_region_base_def(void) { return cm_region_base_def; }
PROOF thm get_cm_retire_region_def(void) {
  return cm_retire_region_def;
}
PROOF thm get_cm_restore_regions_def(void) {
  return cm_restore_regions_def;
}
PROOF thm get_cm_restore_init_def(void) {
  return cm_restore_init_def;
}
PROOF thm get_cm_restore_tagged_def(void) {
  return cm_restore_tagged_def;
}
PROOF thm get_cm_store_width_def(void) {
  return cm_store_width_def;
}
PROOF thm_list get_cm_state_core_defs(void) {
  return THM_LIST(
      cm_state_mem_def, cm_state_init_def, cm_state_tags_def,
      cm_state_tagged_def, cm_state_env_def, cm_state_input_def,
      cm_state_output_def, cm_state_fp_def, cm_state_nextgen_def,
      cm_state_regions_def, cm_state_make_def, cm_state_io_def,
      cm_state_env_set_def, cm_state_frame_def);
}
PROOF thm get_cm_state_io_def(void) { return cm_state_io_def; }
PROOF thm get_cm_state_make_def(void) { return cm_state_make_def; }
PROOF thm get_cm_state_tagged_def(void) {
  return cm_state_tagged_def;
}
PROOF thm get_cm_state_fp_def(void) {
  return cm_state_fp_def;
}
PROOF thm get_cm_state_input_def(void) {
  return cm_state_input_def;
}
PROOF thm get_cm_state_output_def(void) {
  return cm_state_output_def;
}
PROOF thm get_cm_state_nextgen_def(void) {
  return cm_state_nextgen_def;
}
PROOF thm get_cm_state_regions_def(void) {
  return cm_state_regions_def;
}
PROOF thm get_cm_store_mem_def(void) { return cm_store_mem_def; }
PROOF thm get_cm_mark_init_def(void) { return cm_mark_init_def; }
PROOF thm get_cm_clear_init_def(void) { return cm_clear_init_def; }
PROOF thm get_cm_clear_tagged_def(void) {
  return cm_clear_tagged_def;
}
PROOF thm get_cm_write_bytes_def(void) { return cm_write_bytes_def; }
PROOF thm get_cm_static_global_init_bytes_def(void) {
  return cm_static_global_init_bytes_def;
}
PROOF thm get_cm_static_global_bytes_def(void) {
  return cm_static_global_bytes_def;
}
PROOF thm get_cm_static_globals_bytes_def(void) {
  return cm_static_globals_bytes_def;
}
PROOF thm get_cm_static_strings_bytes_def(void) {
  return cm_static_strings_bytes_def;
}
PROOF thm get_cm_static_data_bytes_def(void) {
  return cm_static_data_bytes_def;
}
PROOF thm get_cm_initial_mem_def(void) { return cm_initial_mem_def; }
PROOF thm get_cm_bytes_initialized_def(void) {
  return cm_bytes_initialized_def;
}
PROOF thm get_cm_load_ok_def(void) { return cm_load_ok_def; }
PROOF thm get_cm_load_value_def(void) { return cm_load_value_def; }
PROOF thm get_cm_store_ok_def(void) { return cm_store_ok_def; }
PROOF thm get_cm_state_store_def(void) { return cm_state_store_def; }
PROOF thm get_cm_call_ok_def(void) { return cm_call_ok_def; }
PROOF thm get_cm_is_call_frame_def(void) {
  return cm_is_call_frame_def;
}
PROOF thm get_cm_call_depth_def(void) {
  return cm_call_depth_def;
}
PROOF thm get_cm_begin_call_def(void) { return cm_begin_call_def; }
PROOF thm get_cm_binding_array_def(void) {
  return cm_binding_array_def;
}
PROOF thm get_cm_member_array_def(void) {
  return cm_member_array_def;
}
PROOF thm get_cm_args_start_def(void) { return cm_rstart_def; }
PROOF thm get_cm_binding_address_ok_def(void) {
  return cm_binding_address_ok_def;
}
PROOF thm get_cm_rstart_def(void) { return cm_rstart_def; }
PROOF thm get_cm_lstart_def(void) { return cm_lstart_def; }
PROOF thm get_cm_sstart_def(void) { return cm_sstart_def; }
PROOF thm get_cm_vapply_def(void) { return cm_vapply_def; }
PROOF thm get_cm_capply_def(void) { return cm_capply_def; }
PROOF thm get_cm_control_kind_def(void) {
  return cm_control_kind_def;
}
PROOF thm get_cm_control_value_def(void) {
  return cm_control_value_def;
}
PROOF thm get_cm_control_status_def(void) {
  return cm_control_status_def;
}
PROOF thm get_cm_success_control_def(void) {
  return cm_success_control_def;
}
PROOF thm get_cm_outcome_state_def(void) {
  return cm_outcome_state_def;
}
PROOF thm get_cm_outcome_control_def(void) {
  return cm_outcome_control_def;
}
PROOF thm get_cm_outcome_status_def(void) {
  return cm_outcome_status_def;
}
PROOF thm get_cm_step_def(void) { return cm_step_def; }
PROOF thm get_cm_task_done_def(void) {
  return cm_task_done_def;
}
PROOF thm get_cm_regions_for_slots_def(void) {
  return cm_regions_for_slots_def;
}
PROOF thm get_cm_global_regions_def(void) {
  return cm_global_regions_def;
}
PROOF thm get_cm_string_regions_def(void) {
  return cm_string_regions_def;
}

PROOF thm_list get_cm_runtime_defs(void) {
  return THM_LIST(
      cm_slot_ty_def, cm_slot_count_def,
      cm_global_ty_def, cm_global_count_def,
      cm_global_has_init_def, cm_global_init_def,
      cm_string_bytes_def,
      cm_function_ret_def, cm_function_params_def,
      cm_function_locals_def, cm_function_body_def,
      cm_region_gen_def, cm_region_base_field_def,
      cm_region_lo_def, cm_region_hi_def,
      cm_region_writable_def, cm_region_live_def,
      cm_program_structs_def, cm_program_globals_def,
      cm_program_strings_def, cm_program_functions_def,
      cm_program_main_def, cm_type_size_def, cm_slot_size_def,
      cm_slots_size_def, cm_frame_size_def, cm_temp_slots_def,
      cm_stemps_def, cm_ltemps_def, cm_rtemps_def,
      cm_expr_tpair_def, cm_tleft_def, cm_tright_def,
      cm_slots_prefix_def, cm_globals_prefix_def, cm_strings_prefix_def,
      cm_global_address_def, cm_string_address_def,
      cm_global_generation_def, cm_string_generation_def,
      cm_global_pointer_def, cm_string_pointer_def,
      cm_state_mem_def, cm_state_init_def, cm_state_tags_def,
      cm_region_base_def,
      cm_state_tagged_def, cm_state_env_def, cm_state_input_def,
      cm_state_output_def, cm_state_fp_def, cm_state_nextgen_def,
      cm_state_regions_def, cm_state_make_def, cm_state_io_def,
      cm_state_env_set_def, cm_state_frame_def,
      cm_state_store_def, cm_store_mem_def, cm_store_width_def,
      cm_mark_init_def, cm_clear_init_def, cm_clear_tagged_def,
      cm_bytes_initialized_def,
      cm_store_ok_def, cm_load_ok_def, cm_load_value_def,
      cm_value_type_def, cm_value_number_def, cm_pointer_retype_def,
      cm_is_pointer_def, cm_is_struct_def, cm_convert_value_def,
      cm_truth_def, cm_binary_ok_def, cm_binary_value_def,
      cm_ptr_offset_def, cm_ptr_gen_def, cm_ptr_lo_def,
      cm_ptr_hi_def, cm_ptr_view_def, cm_is_null_value_def,
      cm_pointer_region_ok_def, cm_pointer_live_def,
      cm_pointer_writable_def, cm_pointer_compatible_def,
      cm_pointer_equality_ok_def, cm_ptr_diff_ok_def,
      cm_unary_value_def, cm_ptr_shift_ok_def, cm_ptr_add_def,
      cm_ptr_member_ok_def, cm_ptr_member_def,
      cm_initial_state_def, cm_initial_mem_def,
      cm_static_data_bytes_def, cm_static_strings_bytes_def,
      cm_static_globals_bytes_def, cm_static_global_bytes_def,
      cm_static_global_init_bytes_def, cm_write_bytes_def,
      cm_global_regions_def, cm_string_regions_def,
      cm_first_dynamic_generation_def, cm_regions_for_slots_def,
      cm_param_base_def, cm_local_base_def, cm_call_env_def,
      cm_call_base_state_def, cm_store_params_def, cm_enter_call_def,
      cm_activate_local_def, cm_retire_region_def,
      cm_restore_regions_def, cm_restore_init_def,
      cm_restore_tagged_def, cm_restore_scope_def, cm_restore_call_def,
      cm_is_call_frame_def, cm_call_depth_def,
      cm_call_ok_def, cm_begin_call_def,
      cm_binding_array_def, cm_member_slot_def, cm_member_array_def,
      cm_binding_address_ok_def,
      cm_rstart_def, cm_lstart_def, cm_sstart_def,
      cm_vapply_def, cm_capply_def, cm_control_kind_def,
      cm_control_value_def, cm_control_status_def,
      cm_step_def, cm_task_done_def, cm_task_outcome_def,
      cm_iter_def, cm_outcome_state_def, cm_outcome_control_def,
      cm_outcome_status_def, cm_valid_input_def,
      cm_success_control_def, cm_source_terminates_def);
}
PROOF thm_list get_cm_wf_eval_defs(void) {
  thm_list rules = get_cm_runtime_defs();
  thm_list wf_rules = THM_LIST(
      cm_struct_members_def, cm_leaf_size_def,
      cm_struct_member_size_def, cm_struct_slots_size_def,
      cm_member_offset_slots_def, cm_member_offset_def,
      cm_global_size_def, cm_globals_size_def, cm_strings_size_def,
      cm_static_size_def, cm_tleft_def, cm_tright_def,
      cm_acount_def, cm_adepth_def, cm_imax_def,
      cm_expr_tpair_def, cm_args_temps_def,
      cm_type_depth_def, cm_type_strip_def,
      cm_type_base_code_def, cm_type_code_wf_def,
      cm_type_base_decode_def, cm_add_ptrs_def,
      cm_type_encode_def, cm_type_decode_def,
      cm_type_refs_def, cm_is_pointer_def, cm_is_struct_def,
      cm_pointee_def, cm_struct_id_def, cm_scalar_type_def,
      cm_slot_expr_type_def, cm_global_expr_type_def,
      cm_convertible_def, cm_expr_type_def, cm_integer_type_def,
      cm_scalar_expr_type_def, cm_zero_literal_def,
      cm_expr_convertible_def, cm_lvalue_def,
      cm_binding_type_def, cm_binding_valid_def,
      cm_binary_types_def, cm_unary_types_def,
      cm_member_type_def, cm_member_valid_def, cm_expr_array_def,
      cm_expr_wf_def, cm_decl_count_def, cm_stmt_wf_def,
      cm_slot_wf_def, cm_slots_wf_def, cm_params_wf_def,
      cm_struct_wf_def, cm_global_wf_def, cm_string_wf_def,
      cm_expr_scope_wf_def, cm_scope_add_def,
      cm_stmt_scope_result_def, cm_stmt_scope_wf_def,
      cm_function_wf_def, cm_typed_program_def);
  for (size_t i = 0; i < vector_size(wf_rules); ++i) {
    vector_add(&rules, wf_rules[i]);
  }
  return rules;
}

PROOF static int _cmc_lang_audit(void) {
  thm_list pubs = THM_LIST(
      cm_type_RECURSION, cm_value_RECURSION, cm_expr_RECURSION,
      cm_stmt_RECURSION, cm_program_RECURSION, cm_task_RECURSION,
      cm_outcome_RECURSION,
      cm_type_size_def, cm_slot_size_def, cm_member_offset_def,
      cm_struct_size_def, cm_static_size_def, cm_frame_size_def,
      cm_ltemps_def, cm_rtemps_def, cm_args_temps_def, cm_stemps_def,
      cm_temp_slots_def, cm_type_encode_def, cm_type_decode_def,
      cm_type_roundtrip, cm_expr_wf_def, cm_stmt_wf_def,
      cm_function_wf_def, cm_typed_program_def, cm_source_safe_def,
      cm_exec_closed_def, cm_exec_def, cm_exec_done, cm_exec_rule,
      cm_exec_induct, cm_exec_deterministic, cm_exec_step_inv,
      get_cm_exec_witness(), get_cm_done_step(),
      cm_exec_skip, cm_exec_const, cm_exec_skip_inv, cm_exec_const_inv,
      cm_source_terminates_def);
  for (size_t i = 0; i < vector_size(pubs); ++i) {
    ENSURE_COND(!IS_NULL(pubs[i]),
                "cmc_lang theorem %zu is empty", i);
    ENSURE_COND(vector_size(hyp(pubs[i])) == 0,
                "cmc_lang theorem %zu has hypotheses", i);
  }
  ENSURE_COND(alpha_compare(concl(get_cm_exec_witness()),
      `!(task:cm_task) (out:cm_outcome).
         cm_exec task out ==>
         ?n st ctl status.
           cm_iter n task ==
             CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int) &&
           out == CMOutcome st ctl status`) == 0,
      "cmc_lang execution witness has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(get_cm_done_step()),
      `!(task:cm_task). cm_task_done task ==> cm_step task == task`) == 0,
      "cmc_lang terminal step has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(cm_type_roundtrip),
      `!(ty:cm_type). cm_type_code_wf ty ==>
         cm_type_decode (cm_type_encode ty) == ty`) == 0,
      "cmc_lang type roundtrip has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(cm_exec_done),
      `!st ctl status.
         cm_exec
           (CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int))
           (CMOutcome st ctl status)`) == 0,
      "cmc_lang done rule has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(cm_exec_rule),
      `!task out. cm_exec (cm_step (task:cm_task)) (out:cm_outcome) ==>
         cm_exec task out`) == 0,
      "cmc_lang step rule has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(cm_exec_induct),
      `!P. cm_exec_closed P ==>
        (!task out. cm_exec task out ==>
          P (task:cm_task) (out:cm_outcome))`) == 0,
      "cmc_lang induction rule has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(cm_exec_deterministic),
      `!task out1 out2.
         cm_exec (task:cm_task) (out1:cm_outcome) ==>
         cm_exec task (out2:cm_outcome) ==> out1 == out2`) == 0,
      "cmc_lang determinism theorem has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(cm_exec_skip),
      `!p fid st ks out.
         cm_exec
           (CMCTask (p:cm_program) (fid:int) CMNormal
             (st:cm_src_state) (ks:(cm_frame)list))
           (out:cm_outcome) ==>
         cm_exec (CMSTask p fid CMSkipS st ks) out`) == 0,
      "cmc_lang skip rule has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(cm_exec_const),
      `!p fid n st ks out.
         cm_exec
           (CMVTask (p:cm_program) (fid:int)
             (CMIntV (tower_wrap64 (n:int)))
             (st:cm_src_state) (ks:(cm_frame)list))
           (out:cm_outcome) ==>
         cm_exec
           (CMRTask p fid (CMConstE n CMIntTy) st ks) out`) == 0,
      "cmc_lang constant rule has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(cm_exec_skip_inv),
      `!p fid st ks out.
         cm_exec
           (CMSTask (p:cm_program) (fid:int) CMSkipS
             (st:cm_src_state) (ks:(cm_frame)list))
           (out:cm_outcome) ==>
         cm_exec (CMCTask p fid CMNormal st ks) out`) == 0,
      "cmc_lang skip inversion has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(cm_exec_const_inv),
      `!p fid n st ks out.
         cm_exec
           (CMRTask (p:cm_program) (fid:int)
             (CMConstE (n:int) CMIntTy)
             (st:cm_src_state) (ks:(cm_frame)list))
           (out:cm_outcome) ==>
         cm_exec
           (CMVTask p fid (CMIntV (tower_wrap64 n)) st ks) out`) == 0,
      "cmc_lang constant inversion has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(cm_source_terminates_def),
      `cm_source_terminates (p:cm_program) (input:(int)list)
         (output:(int)list) (status:int) <=>
         (cm_valid_input input && tower_byte_value status &&
          ?st ctl.
            cm_exec (CMStartTask p input)
              (CMOutcome (st:cm_src_state) (ctl:cm_control) status) &&
            cm_success_control ctl &&
            cm_state_output st == output)`) == 0,
      "cmc_lang termination definition has the wrong conclusion");
  ENSURE_COND(vector_size(get_all_axioms()) == _cmc_lang_axioms_before,
              "cmc_lang introduced an axiom");
  return 0;
err:
  ERR_FUN_PUTS("_cmc_lang_audit");
  return -1;
}
PROOF int _cmc_lang_audit_run = _cmc_lang_audit();

PROOF thm get_cm_global_ty_def(void) { return cm_global_ty_def; }
PROOF thm get_cm_global_count_def(void) { return cm_global_count_def; }
PROOF thm get_cm_global_has_init_def(void) {
  return cm_global_has_init_def;
}
PROOF thm get_cm_global_init_def(void) { return cm_global_init_def; }
PROOF thm get_cm_string_bytes_def(void) { return cm_string_bytes_def; }
PROOF thm get_cm_global_size_def(void) { return cm_global_size_def; }
PROOF thm get_cm_globals_size_def(void) { return cm_globals_size_def; }
PROOF thm get_cm_strings_size_def(void) { return cm_strings_size_def; }
PROOF thm get_cm_is_struct_def(void) { return cm_is_struct_def; }
PROOF thm get_cm_struct_id_def(void) { return cm_struct_id_def; }
PROOF thm get_cm_scalar_type_def(void) { return cm_scalar_type_def; }
PROOF thm get_cm_slot_expr_type_def(void) { return cm_slot_expr_type_def; }
PROOF thm get_cm_global_expr_type_def(void) {
  return cm_global_expr_type_def;
}
PROOF thm get_cm_binding_type_def(void) { return cm_binding_type_def; }
PROOF thm get_cm_member_type_def(void) { return cm_member_type_def; }
PROOF thm get_cm_binary_types_def(void) { return cm_binary_types_def; }
PROOF thm get_cm_unary_types_def(void) { return cm_unary_types_def; }
PROOF thm get_cm_global_wf_def(void) { return cm_global_wf_def; }
