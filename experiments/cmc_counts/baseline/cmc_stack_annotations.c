#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_codegen.h"
#require "cmc_codegen.c"
#include "cmc_stack_annotations.h"

PROOF static size_t _cmc_stack_annotations_axioms_before = vector_size(get_all_axioms());

/* A second pass computes annotations from the emitted instructions.  It does
 * not inspect source temporary-count functions or the structural bound.
 * Function-entry resets are obtained from emitted entry PCs and arities. */
PROOF thm cm_function_arity_at_pc_from_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid pc.
       cm_function_arity_at_pc_from (p:cm_program)
         ([]:(cm_function_d)list) (fid:int) (pc:int) = --1i) &&
     (!p fid pc fn rest.
       cm_function_arity_at_pc_from p
         ((fn:cm_function_d) :: (rest:(cm_function_d)list))
         (fid:int) (pc:int) =
       (if pc == cm_function_pc p fid
        then ilength (cm_function_params fn)
        else cm_function_arity_at_pc_from p rest (fid + 1i) pc))`);
PROOF thm cm_function_arity_at_pc_def = new_fun_definition(
    `cm_function_arity_at_pc (p:cm_program) (pc:int) : int =
       cm_function_arity_at_pc_from p
         (cm_program_functions p) 0i pc`);
PROOF thm cm_stack_reset_height_def = new_fun_definition(
    `cm_stack_reset_height (p:cm_program) (pc:int)
       (incoming:int) : int =
       (let arity = cm_function_arity_at_pc p pc in
        if 0i <= arity then arity else incoming)`);
PROOF thm cm_stack_linear_next_def = new_fun_definition(
    `cm_stack_linear_next (inst:tvm_inst) (height:int) : int =
       (let op = tvm_inst_op inst in
        if op == TVMPushOp || op == TVMDupOp || op == TVMGetcOp
        then height + 1i
        else if op == TVMPopOp || op == TVMPutcOp || op == TVMPutiOp
        then height - 1i
        else if op == TVMStoreOp || op == TVMStoreBOp
        then height - 2i
        else if op == TVMAddOp || op == TVMSubOp ||
                op == TVMMulOp || op == TVMDivOp ||
                op == TVMModOp || op == TVMEqOp ||
                op == TVMNeOp || op == TVMLtOp ||
                op == TVMLeOp || op == TVMGtOp ||
                op == TVMGeOp || op == TVMJzOp || op == TVMJnzOp
        then height - 1i
        else if op == TVMCallOp
        then 1i
        else if op == TVMJmpOp || op == TVMRetOp || op == TVMHaltOp
        then 0i
        else height)`);
PROOF thm cm_stack_scan_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p pc incoming.
       cm_stack_scan (p:cm_program) (pc:int) (incoming:int)
         ([]:(tvm_inst)list) = ([]:(int)list)) &&
     (!p pc incoming inst rest.
       cm_stack_scan p pc incoming
         ((inst:tvm_inst) :: (rest:(tvm_inst)list)) =
       (let height = cm_stack_reset_height p pc incoming in
        height ::
        cm_stack_scan p (pc + 1i)
          (cm_stack_linear_next inst height) rest))`);
PROOF thm cm_function_entries_from_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid.
       cm_function_entries_from (p:cm_program)
         ([]:(cm_function_d)list) (fid:int) = ([]:(int)list)) &&
     (!p fid fn rest.
       cm_function_entries_from p
         ((fn:cm_function_d) :: (rest:(cm_function_d)list)) fid =
       cm_function_pc p fid ::
       cm_function_entries_from p rest (fid + 1i))`);
PROOF thm cm_function_arities_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_function_arities ([]:(cm_function_d)list) = ([]:(int)list)) &&
     (!fn rest.
       cm_function_arities
         ((fn:cm_function_d) :: (rest:(cm_function_d)list)) =
       ilength (cm_function_params fn) ::
       cm_function_arities rest)`);
PROOF thm cm_codegen_stack_heights_def = new_fun_definition(
    `cm_codegen_stack_heights (p:cm_program) : (int)list =
       cm_stack_scan p 0i 0i (cm_model_code p)`);
PROOF thm cm_codegen_function_entries_def = new_fun_definition(
    `cm_codegen_function_entries (p:cm_program) : (int)list =
       cm_function_entries_from p (cm_program_functions p) 0i`);
PROOF thm cm_codegen_function_arities_def = new_fun_definition(
    `cm_codegen_function_arities (p:cm_program) : (int)list =
       cm_function_arities (cm_program_functions p)`);

PROOF int _e_cm_codegen_stack_heights =
    cst_add_const_to_header(`cm_codegen_stack_heights`);

PROOF static thm cm_prove_stack_scan_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(code:(tvm_inst)list). !(p:cm_program) pc incoming.
         ilength (cm_stack_scan p pc incoming code) ==
         ilength code`);
  gnode_list cases = INDUCT_TAC(root, `code:(tvm_inst)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        cm_stack_scan_def, get_theorem_by_name("ILENGTH_DEF")));
  }
  return gnode_prove(root);
}
PROOF thm cm_stack_scan_length = cm_prove_stack_scan_length();

PROOF static thm cm_prove_entries_arities_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list). !(p:cm_program) fid.
         ilength
           (cm_function_entries_from p functions fid) ==
         ilength (cm_function_arities functions)`);
  gnode_list cases =
      INDUCT_TAC(root, `functions:(cm_function_d)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        cm_function_entries_from_def, cm_function_arities_def,
        get_theorem_by_name("ILENGTH_DEF")));
  }
  return gnode_prove(root);
}
PROOF thm cm_entries_arities_length =
    cm_prove_entries_arities_length();

PROOF static thm cm_prove_codegen_heights_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         ilength (cm_codegen_stack_heights p) ==
         ilength (cm_model_code p)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_codegen_stack_heights_def, cm_stack_scan_length)));
  return gnode_prove(root);
}
PROOF thm cm_codegen_heights_length =
    cm_prove_codegen_heights_length();

PROOF indtype cm_height_pair_ty = new_datatype_definition(
    "cm_height_pair = CMHeightPair (int)list (int)list");
PROOF static int _t_cm_height_pair =
    cst_add_type_to_header("cm_height_pair", 0);
PROOF static int _c_CMHeightPair = cst_add_const_to_header(
    `CMHeightPair:(int)list->(int)list->cm_height_pair`);
PROOF thm cm_lheights_of_def = new_rec_definition(
    cm_height_pair_ty.rec,
    `cm_lheights_of
       (CMHeightPair (left:(int)list) (right:(int)list)) = left`);
PROOF thm cm_rheights_of_def = new_rec_definition(
    cm_height_pair_ty.rec,
    `cm_rheights_of
       (CMHeightPair (left:(int)list) (right:(int)list)) = right`);

PROOF thm cm_fp_address_heights_def = new_fun_definition(
    `cm_fp_address_heights (height:int) : (int)list =
       [height; height + 1i; height + 1i; height + 2i]`);
PROOF thm cm_temp_access_heights_def = new_fun_definition(
    `cm_temp_access_heights (height:int) : (int)list =
       [height; height + 1i; height + 1i;
        height + 2i; height + 1i]`);
PROOF thm cm_normalize_heights_def = new_fun_definition(
    `cm_normalize_heights (ty:cm_type) (height:int) : (int)list =
       (if ty == CMCharTy
        then [height; height + 1i; height; height + 1i;
              height; height + 1i]
        else [])`);
PROOF thm cm_binding_address_heights_def = new_fun_definition(
    `cm_binding_address_heights (scope:int) : (int)list =
       (if scope == 0i then [0i] else [0i; 1i; 1i; 2i])`);
PROOF thm cm_binary_finish_heights_def = new_fun_definition(
    `cm_binary_finish_heights (p:cm_program) (op:int)
       (left:cm_expr) (right:cm_expr) : (int)list =
       (cm_temp_access_heights 1i ++
        (if op == 8i && cm_is_pointer (cm_expr_type right)
         then [2i; 3i; 2i; 2i]
         else if op == 8i && cm_is_pointer (cm_expr_type left)
         then [2i; 2i; 3i; 2i]
         else if op == 9i &&
                 cm_is_pointer (cm_expr_type left) &&
                 cm_is_pointer (cm_expr_type right)
         then [2i; 2i; 1i; 2i]
         else if op == 9i && cm_is_pointer (cm_expr_type left)
         then [2i; 2i; 3i; 2i]
         else [2i; 2i]))`);

PROOF thm cm_args_reload_heights_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_args_reload_heights (height:int) ([]:(cm_expr)list) = []) &&
     (!height arg args.
       cm_args_reload_heights (height:int)
         ((arg:cm_expr) :: (args:(cm_expr)list)) =
       cm_temp_access_heights height ++
       cm_args_reload_heights (height + 1i) args)`);
PROOF thm cm_expr_heights_def = new_rec_definition(
    get_cm_expr_recursion(),
    `(!p fid n ty.
       cm_expr_heights (p:cm_program) (fid:int)
         (CMConstE (n:int) (ty:cm_type)) =
       CMHeightPair [] [0i]) &&
     (!p fid sid ty.
       cm_expr_heights p fid
         (CMStringE (sid:int) (ty:cm_type)) =
       CMHeightPair [] [0i]) &&
     (!p fid scope slot ty.
       cm_expr_heights p fid
         (CMVarE (scope:int) (slot:int) (ty:cm_type)) =
       CMHeightPair
         (cm_binding_address_heights scope)
         (cm_binding_address_heights scope ++
          (if cm_binding_array p fid scope slot then [] else [1i]))) &&
     (!p fid dst src ty.
       cm_expr_heights p fid
         (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) =
       CMHeightPair []
         (cm_lheights_of (cm_expr_heights p fid dst) ++
          cm_temp_access_heights 1i ++
          cm_rheights_of (cm_expr_heights p fid src) ++
          cm_normalize_heights ty 1i ++
          cm_temp_access_heights 1i ++ [2i] ++
          cm_temp_access_heights 0i ++ [1i])) &&
     (!p fid op left right ty.
       cm_expr_heights p fid
         (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
           (ty:cm_type)) =
       CMHeightPair []
         (if op == 0i || op == 1i
          then cm_rheights_of (cm_expr_heights p fid left) ++
               [1i] ++
               cm_rheights_of (cm_expr_heights p fid right) ++
               [1i; 2i; 1i; 0i]
          else cm_rheights_of (cm_expr_heights p fid left) ++
               cm_temp_access_heights 1i ++
               cm_rheights_of (cm_expr_heights p fid right) ++
               cm_binary_finish_heights p op left right)) &&
     (!p fid op arg ty.
       cm_expr_heights p fid
         (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) =
       (if op == 2i
        then CMHeightPair
          (cm_rheights_of (cm_expr_heights p fid arg))
          (cm_rheights_of (cm_expr_heights p fid arg) ++ [1i])
        else if op == 3i
             then CMHeightPair []
               (cm_lheights_of (cm_expr_heights p fid arg))
             else CMHeightPair []
               (cm_rheights_of (cm_expr_heights p fid arg) ++
                [1i; 2i]))) &&
     (!p fid base index ty.
       cm_expr_heights p fid
         (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) =
       CMHeightPair
         (cm_rheights_of (cm_expr_heights p fid base) ++
          cm_temp_access_heights 1i ++
          cm_rheights_of (cm_expr_heights p fid index) ++
          [1i; 2i] ++ cm_temp_access_heights 1i ++ [2i])
         (cm_rheights_of (cm_expr_heights p fid base) ++
          cm_temp_access_heights 1i ++
          cm_rheights_of (cm_expr_heights p fid index) ++
          [1i; 2i] ++ cm_temp_access_heights 1i ++
          [2i; 1i])) &&
     (!p fid base mid ty.
       cm_expr_heights p fid
         (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) =
       CMHeightPair
         (cm_rheights_of (cm_expr_heights p fid base) ++ [1i; 2i])
         (cm_rheights_of (cm_expr_heights p fid base) ++ [1i; 2i] ++
          (if cm_member_array p (cm_expr_type base) mid
           then [] else [1i]))) &&
     (!p fid callee args ty.
       cm_expr_heights p fid
         (CMCallE (callee:int) (args:(cm_expr)list) (ty:cm_type)) =
       CMHeightPair []
         (cm_args_store_heights p fid args ++
          cm_args_reload_heights 0i args ++ [ilength args])) &&
     (!p fid asked ty.
       cm_expr_heights p fid
         (CMSizeofE (asked:cm_type) (ty:cm_type)) =
       CMHeightPair [] [0i]) &&
     (!p fid ty.
       cm_expr_heights p fid (CMGetcE (ty:cm_type)) =
       CMHeightPair [] [0i]) &&
     (!p fid arg ty.
       cm_expr_heights p fid (CMPutcE (arg:cm_expr) (ty:cm_type)) =
       CMHeightPair []
         (cm_rheights_of (cm_expr_heights p fid arg) ++ [1i; 2i])) &&
     (!p fid arg ty.
       cm_expr_heights p fid (CMPutiE (arg:cm_expr) (ty:cm_type)) =
       CMHeightPair []
         (cm_rheights_of (cm_expr_heights p fid arg) ++ [1i; 2i])) &&
     (!p fid arg ty.
       cm_expr_heights p fid (CMExitE (arg:cm_expr) (ty:cm_type)) =
       CMHeightPair []
         (cm_rheights_of (cm_expr_heights p fid arg) ++
          cm_normalize_heights CMCharTy 1i ++ [1i])) &&
     (!p fid.
       cm_args_store_heights (p:cm_program) (fid:int)
         ([]:(cm_expr)list) = []) &&
     (!p fid arg args.
       cm_args_store_heights p fid
         ((arg:cm_expr) :: (args:(cm_expr)list)) =
       cm_rheights_of (cm_expr_heights p fid arg) ++
       cm_temp_access_heights 1i ++
       cm_args_store_heights p fid args)`);


PROOF thm cm_lvalue_heights_def = new_fun_definition(
    `cm_lvalue_heights (p:cm_program) (fid:int)
       (expr:cm_expr) : (int)list =
       cm_lheights_of (cm_expr_heights p fid expr)`);
PROOF thm cm_rvalue_heights_def = new_fun_definition(
    `cm_rvalue_heights (p:cm_program) (fid:int)
       (expr:cm_expr) : (int)list =
       cm_rheights_of (cm_expr_heights p fid expr)`);


PROOF thm cm_return_heights_def = new_fun_definition(
    `cm_return_heights : (int)list = [1i; 2i; 2i; 2i; 3i; 1i]`);
PROOF thm cm_stmt_heights_def = new_rec_definition(
    get_cm_stmt_recursion(),
    `(!p fid.
       cm_stmt_heights (p:cm_program) (fid:int) CMSkipS = []) &&
     (!p fid expr.
       cm_stmt_heights p fid (CMExprS (expr:cm_expr)) =
       cm_rvalue_heights p fid expr ++ [1i]) &&
     (!p fid slot.
       cm_stmt_heights p fid (CMDeclS (slot:int)) = []) &&
     (!p fid slot expr.
       cm_stmt_heights p fid
         (CMInitS (slot:int) (expr:cm_expr)) =
       cm_rvalue_heights p fid expr ++
       cm_normalize_heights
         (cm_slot_ty
           (inth slot (cm_function_locals
             (inth fid (cm_program_functions p))))) 1i ++
       cm_fp_address_heights 1i ++ [2i]) &&
     (!p fid first second.
       cm_stmt_heights p fid
         (CMSeqS (first:cm_stmt) (second:cm_stmt)) =
       cm_stmt_heights p fid first ++ cm_stmt_heights p fid second) &&
     (!p fid body.
       cm_stmt_heights p fid (CMBlockS (body:cm_stmt)) =
       cm_stmt_heights p fid body) &&
     (!p fid guard yes no.
       cm_stmt_heights p fid
         (CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)) =
       cm_rvalue_heights p fid guard ++ [1i] ++
       cm_stmt_heights p fid yes ++ [0i] ++
       cm_stmt_heights p fid no) &&
     (!p fid guard body.
       cm_stmt_heights p fid
         (CMWhileS (guard:cm_expr) (body:cm_stmt)) =
       cm_rvalue_heights p fid guard ++ [1i] ++
       cm_stmt_heights p fid body ++ [0i]) &&
     (!p fid.
       cm_stmt_heights p fid CMBreakS = [0i]) &&
     (!p fid.
       cm_stmt_heights p fid CMContinueS = [0i]) &&
     (!p fid expr.
       cm_stmt_heights p fid (CMReturnS (expr:cm_expr)) =
       cm_rvalue_heights p fid expr ++
       cm_normalize_heights
         (cm_function_ret
           (inth fid (cm_program_functions p))) 1i ++
       cm_return_heights)`);

PROOF thm cm_fixed_prologue_heights_def = new_fun_definition(
    `cm_fixed_prologue_heights (arity:int) : (int)list =
       [arity; arity + 1i; arity + 1i; arity + 2i;
        arity + 3i; arity + 2i;
        arity; arity + 1i; arity + 1i; arity + 2i;
        arity + 1i; arity + 2i; arity + 3i; arity + 1i]`);
PROOF thm cm_param_store_heights_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!height.
       cm_param_store_heights ([]:(cm_slot_d)list) (height:int) = []) &&
     (!param rest height.
       cm_param_store_heights
         ((param:cm_slot_d) :: (rest:(cm_slot_d)list)) (height:int) =
       cm_param_store_heights rest height ++
       cm_normalize_heights (cm_slot_ty param)
         (height - ilength rest) ++
       cm_fp_address_heights (height - ilength rest) ++
       [height - ilength rest + 1i])`);
PROOF thm cm_prologue_heights_def = new_fun_definition(
    `cm_prologue_heights (f:cm_function_d) : (int)list =
       (let arity = ilength (cm_function_params f) in
        cm_fixed_prologue_heights arity ++
        cm_param_store_heights (cm_function_params f) arity)`);
PROOF thm cm_function_heights_def = new_fun_definition(
    `cm_function_heights (p:cm_program) (fid:int)
       (f:cm_function_d) : (int)list =
       (let actual = inth fid (cm_program_functions p) in
        cm_prologue_heights actual ++
        cm_stmt_heights p fid (cm_function_body actual) ++
        [0i] ++ cm_return_heights)`);
PROOF thm cm_functions_heights_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid.
       cm_functions_heights (p:cm_program) (fid:int)
         ([]:(cm_function_d)list) = []) &&
     (!p fid fn rest.
       cm_functions_heights p fid
         ((fn:cm_function_d) :: (rest:(cm_function_d)list)) =
       cm_function_heights p fid fn ++
       cm_functions_heights p (fid + 1i) rest)`);
PROOF thm cm_prelude_heights_def = new_fun_definition(
    `cm_prelude_heights : (int)list =
       [0i; 1i; 2i; 0i; 1i; 2i; 1i; 2i; 1i; 2i; 1i]`);
PROOF thm cm_codegen_direct_heights_def = new_fun_definition(
    `cm_codegen_direct_heights (p:cm_program) : (int)list =
       cm_prelude_heights ++
       cm_functions_heights p 0i (cm_program_functions p)`);

PROOF static thm cm_prove_ilength_cond_local(void) {
  gnode root = gnode_new_with_ccl(
      `!(b:bool). !(xs:(A)list). !(ys:(A)list).
         ilength (if b then xs else ys) ==
         (if b then ilength xs else ilength ys)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(leaf, `b:bool`, "hb");
  for (size_t i = 0; i < 2; ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF static thm cm_ilength_cond_local =
    cm_prove_ilength_cond_local();

PROOF static thm cm_prove_height_pair_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(b:bool). !(x:cm_height_pair). !(y:cm_height_pair).
         cm_lheights_of (if b then x else y) ==
           (if b then cm_lheights_of x else cm_lheights_of y) &&
         cm_rheights_of (if b then x else y) ==
           (if b then cm_rheights_of x else cm_rheights_of y)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(leaf, `b:bool`, "hb");
  for (size_t i = 0; i < 2; ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF thm cm_height_pair_cond = cm_prove_height_pair_cond();

PROOF static thm cm_prove_count_pair_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(b:bool). !(x:cm_code_counts). !(y:cm_code_counts).
         cm_lcount_of (if b then x else y) ==
           (if b then cm_lcount_of x else cm_lcount_of y) &&
         cm_rcount_of (if b then x else y) ==
           (if b then cm_rcount_of x else cm_rcount_of y)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(leaf, `b:bool`, "hb");
  for (size_t i = 0; i < 2; ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF thm cm_count_pair_cond = cm_prove_count_pair_cond();
PROOF static thm cm_prove_args_reload_heights_count(void) {

  gnode root = gnode_new_with_ccl(
      `!(args:(cm_expr)list). !(height:int).
         ilength (cm_args_reload_heights height args) ==
         5i * ilength args`);
  gnode_list cases = INDUCT_TAC(root, `args:(cm_expr)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    gnode opened = CONV_TAC(leaf, once_rewrite_conv(THM_LIST(
        cm_args_reload_heights_def)));
    gnode reduced = CONV_WITH_ASMP_TAC(
        opened, reduce_rewrite_conv, THM_LIST(
          cm_temp_access_heights_def,
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF")));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_args_reload_heights_count =
    cm_prove_args_reload_heights_count();

PROOF static thm cm_prove_emit_args_reload_count(void) {
  gnode root = gnode_new_with_ccl(
      `!(args:(cm_expr)list). !(p:cm_program) fid slot.
         ilength (cm_emit_args_reload p fid slot args) ==
         5i * ilength args`);
  gnode_list cases = INDUCT_TAC(root, `args:(cm_expr)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    gnode opened = CONV_TAC(leaf, once_rewrite_conv(THM_LIST(
        get_cm_emit_args_reload_def())));
    gnode reduced = CONV_WITH_ASMP_TAC(
        opened, reduce_rewrite_conv, THM_LIST(
          get_cm_temp_load_code_def(),
          get_cm_fp_relative_address_code_def(),
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF")));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_emit_args_reload_count =
    cm_prove_emit_args_reload_count();

PROOF static thm cm_prove_expr_height_lengths(void) {
  gnode root = gnode_new_with_ccl(
      `(!(expr:cm_expr).
          (!(p:cm_program) fid.
             ilength
               (cm_lheights_of (cm_expr_heights p fid expr)) ==
             cm_lvalue_code_count p fid expr) &&
          (!(p:cm_program) fid.
             ilength
               (cm_rheights_of (cm_expr_heights p fid expr)) ==
             cm_rvalue_code_count p fid expr)) &&
       (!(args:(cm_expr)list). !(p:cm_program) fid.
          ilength (cm_args_store_heights p fid args) +
          5i * ilength args + 1i ==
          cm_args_code_count_of
            (cm_args_code_counts p fid args))`);
  gnode matched = MATCH_MP_TAC(root, get_cm_expr_induction());
  gnode cursor = CONV_TAC(
      matched, reduce_rewrite_conv(THM_LIST()));
  gnode cases[16];
  for (size_t i = 0; i < 15; ++i) {
    gnode_list split = CONJ_TAC(cursor);
    cases[i] = split[0];
    cursor = split[1];
  }
  cases[15] = cursor;
  for (size_t i = 0; i < 16; ++i) {
    gnode constructor_leaf = AUTO_INTROS_TAC(cases[i]);
    gnode_list frontier = AUTO_ASMP_DESTRUCT_TAC(constructor_leaf);
    gnode leaf = frontier[0];
    gnode_list obligations;
    if (i < 14) {
      obligations = CONJ_TAC(leaf);
    } else {
      obligations = gnode_list_from_array(1, &leaf);
    }
    for (size_t j = 0; j < vector_size(obligations); ++j) {
      gnode quantified = AUTO_INTROS_TAC(obligations[j]);
      gnode reduced = CONV_WITH_ASMP_TAC(
          quantified, reduce_rewrite_conv, THM_LIST(
            cm_expr_heights_def, cm_args_reload_heights_def,
            cm_lheights_of_def, cm_rheights_of_def,
            cm_fp_address_heights_def, cm_temp_access_heights_def,
            cm_normalize_heights_def,
            cm_binding_address_heights_def,
            cm_binary_finish_heights_def,
            cm_args_reload_heights_count,
            get_cm_lvalue_code_count_def(),
            get_cm_rvalue_code_count_def(),
            get_cm_expr_code_counts_def(),
            get_cm_lcount_of_def(), get_cm_rcount_of_def(),
            get_cm_args_code_counts_def(),
            get_cm_args_code_count_of_def(),
            get_cm_args_arity_of_def(),
            get_cm_char_normalize_count_def(),
            get_cm_binding_address_count_def(),
            get_cm_binary_tail_count_def(),
            cm_height_pair_cond, cm_count_pair_cond,
            cm_ilength_cond_local,
            get_theorem_by_name("ILENGTH_APPEND"),
            get_theorem_by_name("ILENGTH_DEF")));
      if (IS_NULL(reduced->solved)) {
        if ((i == 8 && j == 1) || i == 15) {
          thm args_ih = assume_rule(
              `!(p:cm_program) fid.
                 ilength
                   (cm_args_store_heights p fid
                     (a1:(cm_expr)list)) +
                 5i * ilength (a1:(cm_expr)list) + 1i ==
                 cm_args_code_count_of
                   (cm_args_code_counts p fid a1)`);
          thm args_at = specl_rule(
              TERM_LIST(`p:cm_program`, `fid:int`), args_ih);
          ACCEPT_TAC(reduced, mp_rule(
              int_arith_rule(mk_imp(
                concl(args_at), goal_ccl(reduced->g))),
              args_at));
        } else {
          ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_expr_and_args_height_lengths =
    cm_prove_expr_height_lengths();
PROOF thm cm_expr_height_lengths =
    conjunct1_rule(cm_expr_and_args_height_lengths);
PROOF thm cm_args_store_height_length =
    conjunct2_rule(cm_expr_and_args_height_lengths);

PROOF static thm cm_prove_stmt_height_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(stmt:cm_stmt). !(p:cm_program) fid.
         ilength (cm_stmt_heights p fid stmt) ==
         cm_stmt_code_count p fid stmt`);
  gnode_list cases = INDUCT_TAC(root, `stmt:cm_stmt`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode constructor_leaf = AUTO_INTROS_TAC(cases[i]);
    gnode_list frontier = AUTO_ASMP_DESTRUCT_TAC(constructor_leaf);
    gnode quantified = AUTO_INTROS_TAC(frontier[0]);
    gnode opened = CONV_TAC(quantified,
        once_rewrite_conv(THM_LIST(cm_stmt_heights_def)));
    gnode reduced = CONV_WITH_ASMP_TAC(
        opened, reduce_rewrite_conv, THM_LIST(
          get_cm_stmt_code_count_def(),
          cm_rvalue_heights_def, cm_expr_height_lengths,
          cm_normalize_heights_def, cm_fp_address_heights_def,
          cm_return_heights_def,
          get_cm_char_normalize_count_def(),
          cm_ilength_cond_local,
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF")));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_stmt_height_length =
    cm_prove_stmt_height_length();

PROOF static thm cm_prove_param_height_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(params:(cm_slot_d)list). !(height:int).
         ilength (cm_param_store_heights params height) ==
         cm_param_stores_count params`);
  gnode_list cases = INDUCT_TAC(root, `params:(cm_slot_d)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    gnode opened = CONV_TAC(leaf,
        once_rewrite_conv(THM_LIST(
          cm_param_store_heights_def,
          get_cm_param_stores_count_def())));
    gnode reduced = CONV_WITH_ASMP_TAC(
        opened, reduce_rewrite_conv, THM_LIST(
          cm_normalize_heights_def, cm_fp_address_heights_def,
          get_cm_char_normalize_count_def(),
          cm_ilength_cond_local,
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF")));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_param_height_length =
    cm_prove_param_height_length();

PROOF static thm cm_prove_prologue_height_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(f:cm_function_d).
         ilength (cm_prologue_heights f) ==
         cm_function_prologue_count f`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
      cm_prologue_heights_def, cm_fixed_prologue_heights_def,
      cm_param_height_length, get_cm_function_prologue_count_def(),
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("ILENGTH_DEF")));
  return gnode_prove(root);
}
PROOF thm cm_prologue_height_length =
    cm_prove_prologue_height_length();

PROOF static thm cm_prove_function_height_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid f.
         ilength (cm_function_heights p fid (f:cm_function_d)) ==
         cm_function_code_count p fid`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
      cm_function_heights_def, cm_return_heights_def,
      cm_prologue_height_length, cm_stmt_height_length,
      get_cm_function_code_count_def(),
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("ILENGTH_DEF")));
  return gnode_prove(root);
}
PROOF thm cm_function_height_length =
    cm_prove_function_height_length();

PROOF static thm cm_prove_functions_height_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list). !(p:cm_program) fid.
         ilength (cm_functions_heights p fid functions) ==
         cm_functions_code_size p functions fid`);
  gnode_list cases =
      INDUCT_TAC(root, `functions:(cm_function_d)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    gnode opened = CONV_TAC(leaf,
        once_rewrite_conv(THM_LIST(cm_functions_heights_def)));
    gnode reduced = CONV_WITH_ASMP_TAC(
        opened, reduce_rewrite_conv, THM_LIST(
          cm_function_height_length, get_cm_functions_code_size_def(),
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF")));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_functions_height_length =
    cm_prove_functions_height_length();

PROOF static thm cm_prove_direct_heights_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         ilength (cm_codegen_direct_heights p) ==
         cm_model_code_length p`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
      cm_codegen_direct_heights_def, cm_prelude_heights_def,
      cm_functions_height_length, get_cm_model_code_length_def(),
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("ILENGTH_DEF")));
  return gnode_prove(root);
}
PROOF thm cm_direct_heights_length =
    cm_prove_direct_heights_length();

PROOF static thm cm_prove_num_of_int_add_one(void) {
  gnode root = gnode_new_with_ccl(
      `!(x:int). 0i <= x ==>
         num_of_int (1i + x) == SUC (num_of_int x)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm hx = assume_rule(`0i <= (x:int)`);
  thm h1 = int_arith_rule(`0i <= 1i`);
  thm add = mp_rule(specl_rule(TERM_LIST(`1i`, `x:int`),
      get_theorem_by_name("NUM_OF_INT_ADD")), conj_rule(h1, hx));
  thm reduced_add = pure_rewrite_rule(THM_LIST(
      get_theorem_by_name("NUM_OF_INT_OF_NUM")), add);
  thm commute = specl_rule(TERM_LIST(
      `1`, `num_of_int (x:int)`), get_theorem_by_name("ADD_SYM"));
  thm successor = sym_rule(spec_rule(
      `num_of_int (x:int)`, get_theorem_by_name("ADD1")));
  ACCEPT_TAC(leaf, trans_rule(
      reduced_add, trans_rule(commute, successor)));
  return gnode_prove(root);
}
PROOF thm cm_num_of_int_add_one =
    cm_prove_num_of_int_add_one();

PROOF static thm cm_prove_inth_append_right(void) {
  gnode root = gnode_new_with_ccl(
      `!(prefix:(A)list). !(suffix:(A)list) (i:int).
         0i <= i ==>
         inth (ilength prefix + i) (prefix ++ suffix) ==
         inth i suffix`);
  gnode_list cases = INDUCT_TAC(root, `prefix:(A)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("APPEND"))));
    if (IS_NULL(reduced->solved)) {
      thm zero_index = int_arith_rule(`0i + (i:int) == i`);
      ACCEPT_TAC(reduced, beta_norm(ap_term_rule(
          `\index:int. inth index (suffix:(A)list)`, zero_index)));
    }
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm hi = assume_rule(`0i <= (i:int)`);
    thm ih = assume_rule(
        `!(suffix:(A)list) (i:int).
           0i <= i ==>
           inth (ilength (a1:(A)list) + i)
             (a1 ++ suffix) == inth i suffix`);
    thm ih_at = mp_rule(specl_rule(
        TERM_LIST(`suffix:(A)list`, `i:int`), ih), hi);
    thm hlen = spec_rule(`a1:(A)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm hsum = mp_rule(int_arith_rule(mk_imp(
        mk_conj(concl(hlen), concl(hi)),
        `0i <= ilength (a1:(A)list) + (i:int)`)),
        conj_rule(hlen, hi));
    thm succ = mp_rule(spec_rule(
        `ilength (a1:(A)list) + (i:int)`,
        cm_num_of_int_add_one), hsum);
    thm reassoc = int_arith_rule(
        `(1i + ilength (a1:(A)list)) + (i:int) ==
         1i + (ilength a1 + i)`);
    thm num_reassoc = ap_term_rule(`num_of_int:int->num`, reassoc);
    thm num_succ = trans_rule(num_reassoc, succ);
    thm ih_nth = pure_rewrite_rule(
        THM_LIST(get_theorem_by_name("INTH_DEF")), ih_at);
    gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("INTH_DEF"),
        num_succ, get_theorem_by_name("NTH_DEF"))));
    ACCEPT_TAC(reduced, ih_nth);
  }
  return gnode_prove(root);
}
PROOF thm cm_inth_append_right =
    cm_prove_inth_append_right();

PROOF static thm cm_prove_function_count_nonnegative(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid. 0i <= cm_function_code_count p fid`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm length_nonnegative = ispec_rule(
      `cm_function_heights (p:cm_program) (fid:int)
         (inth fid (cm_program_functions p))`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  thm length_exact = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`,
      `inth (fid:int) (cm_program_functions (p:cm_program))`),
      cm_function_height_length);
  ACCEPT_TAC(leaf, mp_rule(int_arith_rule(mk_imp(
      mk_conj(concl(length_nonnegative), concl(length_exact)),
      goal_ccl(leaf->g))), conj_rule(length_nonnegative, length_exact)));
  return gnode_prove(root);
}
PROOF thm cm_function_code_count_nonnegative =
    cm_prove_function_count_nonnegative();

PROOF static thm cm_prove_function_prefix_nonnegative(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list). !(p:cm_program) index.
         0i <= cm_function_prefix p functions index`);
  gnode_list cases =
      INDUCT_TAC(root, `functions:(cm_function_d)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode constructor_leaf = AUTO_INTROS_TAC(cases[i]);
    gnode_list frontier = AUTO_ASMP_DESTRUCT_TAC(constructor_leaf);
    gnode leaf = frontier[0];
    gnode opened = CONV_TAC(leaf,
        once_rewrite_conv(THM_LIST(get_cm_function_prefix_def())));
    gnode_list branches;
    if (i == 0) {
      branches = gnode_list_from_array(1, &opened);
    } else {
      branches = BOOL_CASES_TAC(
          opened, `(index:int) == 0i`, "hindex");
    }
    for (size_t j = 0; j < vector_size(branches); ++j) {
      gnode reduced = CONV_WITH_ASMP_TAC(
          branches[j], reduce_rewrite_conv, THM_LIST(
            cm_function_code_count_nonnegative));
      if (IS_NULL(reduced->solved)) {
        thm ih = assume_rule(
            `!(p:cm_program) index.
               0i <= cm_function_prefix p
                 (a1:(cm_function_d)list) index`);
        thm tail_nonnegative = specl_rule(TERM_LIST(
            `p:cm_program`, `(index:int) - 1i`), ih);
        thm head_nonnegative = specl_rule(TERM_LIST(
            `p:cm_program`,
            `ilength (cm_program_functions (p:cm_program)) -
             ilength ((a0:cm_function_d) ::
               (a1:(cm_function_d)list))`),
            cm_function_code_count_nonnegative);
        thm facts = conj_rule(head_nonnegative, tail_nonnegative);
        ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
            concl(facts), goal_ccl(reduced->g))), facts));
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_function_prefix_nonnegative =
    cm_prove_function_prefix_nonnegative();

PROOF static thm cm_prove_function_height_head(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid f.
         inth 0i
           (cm_function_heights p fid (f:cm_function_d)) ==
         ilength (cm_function_params
           (inth fid (cm_program_functions p)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_function_heights_def, cm_prologue_heights_def,
      cm_fixed_prologue_heights_def,
      get_theorem_by_name("INTH_DEF"),
      get_theorem_by_name("NUM_OF_INT_OF_NUM"),
      get_theorem_by_name("NTH_DEF"),
      get_theorem_by_name("APPEND"))));
  if (IS_NULL(reduced->solved)) {
    CONV_TAC(reduced, rewrite_conv(THM_LIST()));
  }
  return gnode_prove(root);
}
PROOF thm cm_function_height_head =
    cm_prove_function_height_head();

PROOF static thm cm_prove_function_entry_in_suffix(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list). !(p:cm_program) index.
         0i <= index && index < ilength functions ==>
         inth (cm_function_prefix p functions index)
           (cm_functions_heights p
             (ilength (cm_program_functions p) - ilength functions)
             functions) ==
         ilength (cm_function_params
           (inth
             ((ilength (cm_program_functions p) -
               ilength functions) + index)
             (cm_program_functions p)))`);
  gnode_list cases =
      INDUCT_TAC(root, `functions:(cm_function_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm bounds = assume_rule(
        `0i <= (index:int) &&
         index < ilength ([]:(cm_function_d)list)`);
    thm empty_bounds = pure_rewrite_rule(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF")), bounds);
    thm impossible = mp_rule(int_arith_rule(mk_imp(
        concl(empty_bounds), `F`)), empty_bounds);
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode constructor_leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list frontier = AUTO_ASMP_DESTRUCT_TAC(constructor_leaf);
    gnode leaf = frontier[0];
    thm lower = assume_rule(`0i <= (index:int)`);
    thm upper = assume_rule(
        `(index:int) <
         ilength ((a0:cm_function_d) ::
           (a1:(cm_function_d)list))`);
    thm bounds = conj_rule(lower, upper);
    gnode_list index_cases =
        BOOL_CASES_TAC(leaf, `(index:int) == 0i`, "hindex");
    {
      gnode reduced = CONV_WITH_ASMP_TAC(
          index_cases[0], reduce_rewrite_conv, THM_LIST(
            get_cm_function_prefix_def(), cm_functions_heights_def,
            cm_function_height_head, cm_function_heights_def,
            cm_prologue_heights_def, cm_fixed_prologue_heights_def,
            get_theorem_by_name("ILENGTH_DEF"),
            get_theorem_by_name("INTH_DEF"),
            get_theorem_by_name("NUM_OF_INT_OF_NUM"),
            get_theorem_by_name("NTH_DEF"),
            get_theorem_by_name("APPEND")));
      if (IS_NULL(reduced->solved)) {
        thm index_zero = int_arith_rule(
            `(ilength (cm_program_functions (p:cm_program)) -
               (1i + ilength (a1:(cm_function_d)list))) ==
             (ilength (cm_program_functions p) -
               (1i + ilength a1)) + 0i`);
        ACCEPT_TAC(reduced, beta_norm(ap_term_rule(
            `\entry:int.
               ilength (cm_function_params
                 (NTH (num_of_int entry)
                   (cm_program_functions (p:cm_program))))`,
            index_zero)));
      }
    }
    {
      thm hindex = assume_rule(`~((index:int) == 0i)`);
      thm cons_bounds = pure_rewrite_rule(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF")), bounds);
      thm tail_bounds = mp_rule(int_arith_rule(mk_imp(
          mk_conj(concl(cons_bounds), concl(hindex)),
          `0i <= (index:int) - 1i &&
           index - 1i < ilength (a1:(cm_function_d)list)`)),
          conj_rule(cons_bounds, hindex));
      thm ih = assume_rule(
          `!(p:cm_program) index.
             0i <= index &&
             index < ilength (a1:(cm_function_d)list) ==>
             inth (cm_function_prefix p a1 index)
               (cm_functions_heights p
                 (ilength (cm_program_functions p) - ilength a1) a1) ==
             ilength (cm_function_params
               (inth
                 ((ilength (cm_program_functions p) - ilength a1) +
                   index)
                 (cm_program_functions p)))`);
      thm ih_at = mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `(index:int) - 1i`), ih), tail_bounds);
      thm relative_nonnegative = specl_rule(TERM_LIST(
          `a1:(cm_function_d)list`, `p:cm_program`,
          `(index:int) - 1i`), cm_function_prefix_nonnegative);
      thm split = mp_rule(ispecl_rule(TERM_LIST(
          `cm_function_heights (p:cm_program)
             (ilength (cm_program_functions p) -
               ilength ((a0:cm_function_d) ::
                 (a1:(cm_function_d)list)))
             a0`,
          `cm_functions_heights (p:cm_program)
             ((ilength (cm_program_functions p) -
               ilength ((a0:cm_function_d) ::
                 (a1:(cm_function_d)list))) + 1i)
             a1`,
          `cm_function_prefix p (a1:(cm_function_d)list)
             ((index:int) - 1i)`), cm_inth_append_right),
          relative_nonnegative);
      thm split_exact = pure_rewrite_rule(THM_LIST(
          cm_function_height_length,
          get_theorem_by_name("ILENGTH_DEF")), split);
      thm tail_base = int_arith_rule(
          `(ilength (cm_program_functions (p:cm_program)) -
              (1i + ilength (a1:(cm_function_d)list))) + 1i ==
           ilength (cm_program_functions p) - ilength a1`);
      thm tail_base_equal = beta_norm(ap_term_rule(
          `\fid:int.
             inth
               (cm_function_prefix (p:cm_program)
                 (a1:(cm_function_d)list) ((index:int) - 1i))
               (cm_functions_heights p fid a1)`,
          tail_base));
      thm rhs_index = int_arith_rule(
          `(ilength (cm_program_functions (p:cm_program)) -
              ilength (a1:(cm_function_d)list)) +
             ((index:int) - 1i) ==
           (ilength (cm_program_functions p) -
              (1i + ilength (a1:(cm_function_d)list))) + index`);
      thm rhs_equal = beta_norm(ap_term_rule(
          `\entry:int.
             ilength (cm_function_params
               (inth entry (cm_program_functions (p:cm_program))))`,
          rhs_index));
      thm tail_result = trans_rule(ih_at, rhs_equal);
      thm result = trans_rule(split_exact,
          trans_rule(tail_base_equal, tail_result));
      gnode reduced = CONV_TAC(
          index_cases[1], reduce_rewrite_conv(THM_LIST(
            get_cm_function_prefix_def(), cm_functions_heights_def,
            hindex, get_theorem_by_name("ILENGTH_DEF"))));
      if (IS_NULL(reduced->solved)) {
        ACCEPT_TAC(reduced, result);
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_function_entry_in_suffix =
    cm_prove_function_entry_in_suffix();

PROOF static thm cm_prove_prelude_height_length(void) {
  gnode root = gnode_new_with_ccl(
      `ilength cm_prelude_heights == 11i`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_prelude_heights_def, get_theorem_by_name("ILENGTH_DEF"))));
  return gnode_prove(root);
}
PROOF thm cm_prelude_height_length =
    cm_prove_prelude_height_length();

PROOF static thm cm_prove_function_entry_height(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid.
         0i <= fid &&
         fid < ilength (cm_program_functions p) ==>
         inth (cm_function_pc p fid)
           (cm_codegen_direct_heights p) ==
         ilength (cm_function_params
           (inth fid (cm_program_functions p)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list frontier = AUTO_ASMP_DESTRUCT_TAC(leaf);
  leaf = frontier[0];
  thm lower = assume_rule(`0i <= (fid:int)`);
  thm upper = assume_rule(
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`);
  thm bounds = conj_rule(lower, upper);
  thm suffix = mp_rule(specl_rule(TERM_LIST(
      `cm_program_functions (p:cm_program)`, `p:cm_program`,
      `fid:int`), cm_function_entry_in_suffix), bounds);
  thm prefix_nonnegative = specl_rule(TERM_LIST(
      `cm_program_functions (p:cm_program)`, `p:cm_program`,
      `fid:int`), cm_function_prefix_nonnegative);
  thm split = mp_rule(ispecl_rule(TERM_LIST(
      `cm_prelude_heights:(int)list`,
      `cm_functions_heights (p:cm_program) 0i
         (cm_program_functions p)`,
      `cm_function_prefix (p:cm_program)
         (cm_program_functions p) (fid:int)`),
      cm_inth_append_right), prefix_nonnegative);
  thm cancel = int_arith_rule(`(n:int) - n == 0i`);
  thm cancel_add = int_arith_rule(
      `(n:int) - n + (i:int) == i`);
  thm suffix_normalized = pure_rewrite_rule(
      THM_LIST(cancel, cancel_add), suffix);
  thm result = trans_rule(split, suffix_normalized);
  thm normalized = pure_rewrite_rule(
      THM_LIST(cm_prelude_height_length), result);
  gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_codegen_direct_heights_def, get_cm_function_pc_def())));
  ACCEPT_TAC(reduced, normalized);
  return gnode_prove(root);
}
PROOF thm cm_function_entry_height =
    cm_prove_function_entry_height();
