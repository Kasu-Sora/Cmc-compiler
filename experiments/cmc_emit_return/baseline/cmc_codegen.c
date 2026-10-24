#include "proof/proof.h"
#include "userlib/renderers.h"
#include "cmc_lang.h"
#require "cmc_lang.c"
#include "tvm_model.h"
#require "tvm_model.c"
#include "cmc_codegen.h"
#include "userlib/proof.h"

PROOF static size_t _cmc_codegen_axioms_before =
    vector_size(get_all_axioms());

PROOF indtype cm_code_counts_ty = new_datatype_definition(
    "cm_code_counts = CMCodeCounts int int");
PROOF indtype cm_args_count_ty = new_datatype_definition(
    "cm_args_count = CMArgsCount int int");
PROOF static int _t_cm_code_counts =
    cst_add_type_to_header("cm_code_counts", 0);
PROOF static int _t_cm_args_count =
    cst_add_type_to_header("cm_args_count", 0);
PROOF static int _c_CMCodeCounts = cst_add_const_to_header(
    `CMCodeCounts:int->int->cm_code_counts`);
PROOF static int _c_CMArgsCount = cst_add_const_to_header(
    `CMArgsCount:int->int->cm_args_count`);

PROOF thm cm_lcount_of_def = new_rec_definition(
    cm_code_counts_ty.rec,
    `cm_lcount_of (CMCodeCounts (lcount:int) (rcount:int)) = lcount`);
PROOF thm cm_rcount_of_def = new_rec_definition(
    cm_code_counts_ty.rec,
    `cm_rcount_of (CMCodeCounts (lcount:int) (rcount:int)) = rcount`);
PROOF thm cm_args_code_count_of_def = new_rec_definition(
    cm_args_count_ty.rec,
    `cm_args_code_count_of
       (CMArgsCount (count:int) (arity:int)) = count`);
PROOF thm cm_args_arity_of_def = new_rec_definition(
    cm_args_count_ty.rec,
    `cm_args_arity_of
       (CMArgsCount (count:int) (arity:int)) = arity`);
PROOF int _e_cm_lcount_of =
    cst_add_const_to_header(`cm_lcount_of`);
PROOF int _e_cm_rcount_of =
    cst_add_const_to_header(`cm_rcount_of`);
PROOF int _e_cm_args_code_count_of =
    cst_add_const_to_header(`cm_args_code_count_of`);
PROOF int _e_cm_args_arity_of =
    cst_add_const_to_header(`cm_args_arity_of`);

PROOF thm cm_char_normalize_count_def = new_fun_definition(
    `cm_char_normalize_count (ty:cm_type) : int =
       (if ty == CMCharTy then 6i else 0i)`);
PROOF thm cm_binding_address_count_def = new_fun_definition(
    `cm_binding_address_count (scope:int) : int =
       (if scope == 0i then 1i else 4i)`);
PROOF thm cm_binary_tail_count_def = new_fun_definition(
    `cm_binary_tail_count (p:cm_program) (op:int)
       (left:cm_expr) (right:cm_expr) : int =
       (10i +
        (if op == 8i && cm_is_pointer (cm_expr_type right)
         then 4i
         else 1i +
           (if op == 8i && cm_is_pointer (cm_expr_type left)
            then 3i
            else if op == 9i &&
                    cm_is_pointer (cm_expr_type left) &&
                    cm_is_pointer (cm_expr_type right)
            then 3i
            else if op == 9i && cm_is_pointer (cm_expr_type left)
            then 3i else 1i)))`);
PROOF int _e_cm_char_normalize_count =
    cst_add_const_to_header(`cm_char_normalize_count`);
PROOF int _e_cm_binding_address_count =
    cst_add_const_to_header(`cm_binding_address_count`);

PROOF thm cm_expr_code_counts_def = new_rec_definition(
    get_cm_expr_recursion(),
    `(!p fid n ty.
       cm_expr_code_counts (p:cm_program) (fid:int)
         (CMConstE (n:int) (ty:cm_type)) =
         CMCodeCounts 0i 1i) &&
     (!p fid sid ty.
       cm_expr_code_counts (p:cm_program) (fid:int)
         (CMStringE (sid:int) (ty:cm_type)) =
         CMCodeCounts 0i 1i) &&
     (!p fid scope slot ty.
       cm_expr_code_counts (p:cm_program) (fid:int)
         (CMVarE (scope:int) (slot:int) (ty:cm_type)) =
         CMCodeCounts (cm_binding_address_count scope)
           (cm_binding_address_count scope +
            (if cm_binding_array p fid scope slot then 0i else 1i))) &&
     (!p fid dst src ty.
       cm_expr_code_counts (p:cm_program) (fid:int)
         (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) =
         CMCodeCounts 0i
           (cm_lcount_of (cm_expr_code_counts p fid dst) +
            5i + cm_rcount_of (cm_expr_code_counts p fid src) +
            cm_char_normalize_count ty + 12i)) &&
     (!p fid op left right ty.
       cm_expr_code_counts (p:cm_program) (fid:int)
         (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
           (ty:cm_type)) =
         CMCodeCounts 0i
           (if op == 0i || op == 1i
            then cm_rcount_of (cm_expr_code_counts p fid left) +
                 cm_rcount_of (cm_expr_code_counts p fid right) + 5i
            else cm_rcount_of (cm_expr_code_counts p fid left) +
                 cm_rcount_of (cm_expr_code_counts p fid right) +
                 cm_binary_tail_count p op left right)) &&
     (!p fid op arg ty.
       cm_expr_code_counts (p:cm_program) (fid:int)
         (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) =
         (if op == 2i
          then CMCodeCounts
            (cm_rcount_of (cm_expr_code_counts p fid arg))
            (cm_rcount_of (cm_expr_code_counts p fid arg) + 1i)
          else if op == 3i
          then CMCodeCounts 0i
            (cm_lcount_of (cm_expr_code_counts p fid arg))
          else CMCodeCounts 0i
            (cm_rcount_of (cm_expr_code_counts p fid arg) + 2i))) &&
     (!p fid base index ty.
       cm_expr_code_counts (p:cm_program) (fid:int)
         (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) =
         CMCodeCounts
           (cm_rcount_of (cm_expr_code_counts p fid base) +
            cm_rcount_of (cm_expr_code_counts p fid index) + 13i)
           (cm_rcount_of (cm_expr_code_counts p fid base) +
            cm_rcount_of (cm_expr_code_counts p fid index) + 14i)) &&
     (!p fid base mid ty.
       cm_expr_code_counts (p:cm_program) (fid:int)
         (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) =
         CMCodeCounts
           (cm_rcount_of (cm_expr_code_counts p fid base) + 2i)
           (cm_rcount_of (cm_expr_code_counts p fid base) + 2i +
            (if cm_member_array p (cm_expr_type base) mid
             then 0i else 1i))) &&
     (!p fid callee args ty.
       cm_expr_code_counts (p:cm_program) (fid:int)
         (CMCallE (callee:int) (args:(cm_expr)list) (ty:cm_type)) =
         CMCodeCounts 0i
           (cm_args_code_count_of
              (cm_args_code_counts p fid args))) &&
     (!p fid asked ty.
       cm_expr_code_counts (p:cm_program) (fid:int)
         (CMSizeofE (asked:cm_type) (ty:cm_type)) =
         CMCodeCounts 0i 1i) &&
     (!p fid ty.
       cm_expr_code_counts (p:cm_program) (fid:int)
         (CMGetcE (ty:cm_type)) = CMCodeCounts 0i 1i) &&
     (!p fid arg ty.
       cm_expr_code_counts (p:cm_program) (fid:int)
         (CMPutcE (arg:cm_expr) (ty:cm_type)) =
         CMCodeCounts 0i
           (cm_rcount_of (cm_expr_code_counts p fid arg) + 2i)) &&
     (!p fid arg ty.
       cm_expr_code_counts (p:cm_program) (fid:int)
         (CMPutiE (arg:cm_expr) (ty:cm_type)) =
         CMCodeCounts 0i
           (cm_rcount_of (cm_expr_code_counts p fid arg) + 2i)) &&
     (!p fid arg ty.
       cm_expr_code_counts (p:cm_program) (fid:int)
         (CMExitE (arg:cm_expr) (ty:cm_type)) =
         CMCodeCounts 0i
           (cm_rcount_of (cm_expr_code_counts p fid arg) + 7i)) &&
     (!p fid.
       cm_args_code_counts (p:cm_program) (fid:int)
         ([]:(cm_expr)list) = CMArgsCount 1i 0i) &&
     (!p fid arg args.
       cm_args_code_counts (p:cm_program) (fid:int)
         ((arg:cm_expr) :: (args:(cm_expr)list)) =
         CMArgsCount
           (cm_rcount_of (cm_expr_code_counts p fid arg) + 10i +
            cm_args_code_count_of (cm_args_code_counts p fid args))
           (1i + cm_args_arity_of (cm_args_code_counts p fid args)))`);
PROOF int _e_cm_expr_code_counts =
    cst_add_const_to_header(`cm_expr_code_counts`);
PROOF int _e_cm_args_code_counts =
    cst_add_const_to_header(`cm_args_code_counts`);

PROOF thm cm_lvalue_code_count_def = new_fun_definition(
    `cm_lvalue_code_count (p:cm_program) (fid:int)
       (expr:cm_expr) : int =
       cm_lcount_of (cm_expr_code_counts p fid expr)`);
PROOF thm cm_rvalue_code_count_def = new_fun_definition(
    `cm_rvalue_code_count (p:cm_program) (fid:int)
       (expr:cm_expr) : int =
       cm_rcount_of (cm_expr_code_counts p fid expr)`);
PROOF int _e_cm_lvalue_code_count =
    cst_add_const_to_header(`cm_lvalue_code_count`);
PROOF int _e_cm_rvalue_code_count =
    cst_add_const_to_header(`cm_rvalue_code_count`);

PROOF thm cm_i32_code_count_def = new_fun_definition(
    `cm_i32_code_count (count:int) : bool =
       (0i <= count && count <= 2147483647i)`);
PROOF thm cm_code_counts_representable_def = new_fun_definition(
    `cm_code_counts_representable (counts:cm_code_counts) : bool =
       (cm_i32_code_count (cm_lcount_of counts) &&
        cm_i32_code_count (cm_rcount_of counts))`);
PROOF thm cm_expr_count_node_representable_def = new_fun_definition(
    `cm_expr_count_node_representable (p:cm_program) (fid:int)
       (expr:cm_expr) : bool =
       (cm_code_counts_representable
          (cm_expr_code_counts p fid expr) &&
        cm_type_code_wf (cm_expr_type expr) &&
        cm_i32_code_count
          (cm_type_encode (cm_expr_type expr)))`);
PROOF int _e_cm_expr_count_node_representable =
    cst_add_const_to_header(`cm_expr_count_node_representable`);
PROOF thm cm_expr_counts_representable_def = new_rec_definition(
    get_cm_expr_recursion(),
    `(!p fid n ty.
       cm_expr_counts_representable (p:cm_program) (fid:int)
         (CMConstE (n:int) (ty:cm_type)) =
       cm_expr_count_node_representable p fid (CMConstE n ty)) &&
     (!p fid sid ty.
       cm_expr_counts_representable (p:cm_program) (fid:int)
         (CMStringE (sid:int) (ty:cm_type)) =
       (cm_expr_count_node_representable p fid (CMStringE sid ty) &&
        cm_i32_code_count sid)) &&
     (!p fid scope slot ty.
       cm_expr_counts_representable (p:cm_program) (fid:int)
         (CMVarE (scope:int) (slot:int) (ty:cm_type)) =
       (cm_expr_count_node_representable p fid (CMVarE scope slot ty) &&
        cm_i32_code_count slot)) &&
     (!p fid dst src ty.
       cm_expr_counts_representable (p:cm_program) (fid:int)
         (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) =
       (cm_expr_count_node_representable p fid
          (CMAssignE dst src ty) &&
        cm_expr_counts_representable p fid dst &&
        cm_expr_counts_representable p fid src)) &&
     (!p fid op left right ty.
       cm_expr_counts_representable (p:cm_program) (fid:int)
         (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
           (ty:cm_type)) =
       (cm_expr_count_node_representable p fid
          (CMBinaryE op left right ty) &&
        cm_expr_counts_representable p fid left &&
        cm_expr_counts_representable p fid right)) &&
     (!p fid op arg ty.
       cm_expr_counts_representable (p:cm_program) (fid:int)
         (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) =
       (cm_expr_count_node_representable p fid
          (CMUnaryE op arg ty) &&
        cm_expr_counts_representable p fid arg)) &&
     (!p fid base index ty.
       cm_expr_counts_representable (p:cm_program) (fid:int)
         (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) =
       (cm_expr_count_node_representable p fid
          (CMIndexE base index ty) &&
        cm_expr_counts_representable p fid base &&
        cm_expr_counts_representable p fid index)) &&
     (!p fid base mid ty.
       cm_expr_counts_representable (p:cm_program) (fid:int)
         (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) =
       (cm_expr_count_node_representable p fid
          (CMMemberE base mid ty) &&
        cm_i32_code_count mid &&
        cm_expr_counts_representable p fid base)) &&
     (!p fid callee args ty.
       cm_expr_counts_representable (p:cm_program) (fid:int)
         (CMCallE (callee:int) (args:(cm_expr)list) (ty:cm_type)) =
       (cm_expr_count_node_representable p fid
          (CMCallE callee args ty) &&
        cm_i32_code_count callee &&
        cm_args_counts_representable p fid args)) &&
     (!p fid asked ty.
       cm_expr_counts_representable (p:cm_program) (fid:int)
         (CMSizeofE (asked:cm_type) (ty:cm_type)) =
       (cm_expr_count_node_representable p fid
          (CMSizeofE asked ty) &&
        cm_i32_code_count (cm_type_encode asked))) &&
     (!p fid ty.
       cm_expr_counts_representable (p:cm_program) (fid:int)
         (CMGetcE (ty:cm_type)) =
       cm_expr_count_node_representable p fid (CMGetcE ty)) &&
     (!p fid arg ty.
       cm_expr_counts_representable (p:cm_program) (fid:int)
         (CMPutcE (arg:cm_expr) (ty:cm_type)) =
       (cm_expr_count_node_representable p fid (CMPutcE arg ty) &&
        cm_expr_counts_representable p fid arg)) &&
     (!p fid arg ty.
       cm_expr_counts_representable (p:cm_program) (fid:int)
         (CMPutiE (arg:cm_expr) (ty:cm_type)) =
       (cm_expr_count_node_representable p fid (CMPutiE arg ty) &&
        cm_expr_counts_representable p fid arg)) &&
     (!p fid arg ty.
       cm_expr_counts_representable (p:cm_program) (fid:int)
         (CMExitE (arg:cm_expr) (ty:cm_type)) =
       (cm_expr_count_node_representable p fid (CMExitE arg ty) &&
        cm_expr_counts_representable p fid arg)) &&
     (!p fid.
       cm_args_counts_representable (p:cm_program) (fid:int)
         ([]:(cm_expr)list) =
       cm_i32_code_count
         (cm_args_code_count_of (cm_args_code_counts p fid []))) &&
     (!p fid arg args.
       cm_args_counts_representable (p:cm_program) (fid:int)
         ((arg:cm_expr) :: (args:(cm_expr)list)) =
       (cm_i32_code_count
          (cm_args_code_count_of
            (cm_args_code_counts p fid (arg :: args))) &&
        cm_expr_counts_representable p fid arg &&
        cm_args_counts_representable p fid args))`);
PROOF int _e_cm_i32_code_count =
    cst_add_const_to_header(`cm_i32_code_count`);
PROOF int _e_cm_code_counts_representable =
    cst_add_const_to_header(`cm_code_counts_representable`);
PROOF int _e_cm_expr_counts_representable =
    cst_add_const_to_header(`cm_expr_counts_representable`);
PROOF int _e_cm_args_counts_representable =
    cst_add_const_to_header(`cm_args_counts_representable`);

PROOF thm cm_stmt_code_count_def = new_rec_definition(
    get_cm_stmt_recursion(),
    `(!p fid.
       cm_stmt_code_count (p:cm_program) (fid:int) CMSkipS = 0i) &&
     (!p fid expr.
       cm_stmt_code_count (p:cm_program) (fid:int)
         (CMExprS (expr:cm_expr)) =
         cm_rvalue_code_count p fid expr + 1i) &&
     (!p fid slot.
       cm_stmt_code_count (p:cm_program) (fid:int)
         (CMDeclS (slot:int)) = 0i) &&
     (!p fid slot expr.
       cm_stmt_code_count (p:cm_program) (fid:int)
         (CMInitS (slot:int) (expr:cm_expr)) =
         cm_rvalue_code_count p fid expr +
         cm_char_normalize_count
           (cm_slot_ty
             (inth slot (cm_function_locals
               (inth fid (cm_program_functions p))))) + 5i) &&
     (!p fid first second.
       cm_stmt_code_count (p:cm_program) (fid:int)
         (CMSeqS (first:cm_stmt) (second:cm_stmt)) =
         cm_stmt_code_count p fid first +
         cm_stmt_code_count p fid second) &&
     (!p fid body.
       cm_stmt_code_count (p:cm_program) (fid:int)
         (CMBlockS (body:cm_stmt)) =
         cm_stmt_code_count p fid body) &&
     (!p fid guard yes no.
       cm_stmt_code_count (p:cm_program) (fid:int)
         (CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)) =
         cm_rvalue_code_count p fid guard + 1i +
         cm_stmt_code_count p fid yes + 1i +
         cm_stmt_code_count p fid no) &&
     (!p fid guard body.
       cm_stmt_code_count (p:cm_program) (fid:int)
         (CMWhileS (guard:cm_expr) (body:cm_stmt)) =
         cm_rvalue_code_count p fid guard + 1i +
         cm_stmt_code_count p fid body + 1i) &&
     (!p fid.
       cm_stmt_code_count (p:cm_program) (fid:int) CMBreakS = 1i) &&
     (!p fid.
       cm_stmt_code_count (p:cm_program) (fid:int) CMContinueS = 1i) &&
     (!p fid expr.
       cm_stmt_code_count (p:cm_program) (fid:int)
         (CMReturnS (expr:cm_expr)) =
         cm_rvalue_code_count p fid expr +
         cm_char_normalize_count
           (cm_function_ret
             (inth fid (cm_program_functions p))) + 6i)`);
PROOF int _e_cm_stmt_code_count =
    cst_add_const_to_header(`cm_stmt_code_count`);

PROOF thm cm_stmt_counts_representable_def = new_rec_definition(
    get_cm_stmt_recursion(),
    `(!p fid.
       cm_stmt_counts_representable (p:cm_program) (fid:int) CMSkipS =
       cm_i32_code_count (cm_stmt_code_count p fid CMSkipS)) &&
     (!p fid expr.
       cm_stmt_counts_representable (p:cm_program) (fid:int)
         (CMExprS (expr:cm_expr)) =
       (cm_i32_code_count
          (cm_stmt_code_count p fid (CMExprS expr)) &&
        cm_expr_counts_representable p fid expr)) &&
     (!p fid slot.
       cm_stmt_counts_representable (p:cm_program) (fid:int)
         (CMDeclS (slot:int)) =
       cm_i32_code_count
         (cm_stmt_code_count p fid (CMDeclS slot))) &&
     (!p fid slot expr.
       cm_stmt_counts_representable (p:cm_program) (fid:int)
         (CMInitS (slot:int) (expr:cm_expr)) =
       (cm_i32_code_count
          (cm_stmt_code_count p fid (CMInitS slot expr)) &&
        cm_type_code_wf
          (cm_slot_ty
            (inth slot (cm_function_locals
              (inth fid (cm_program_functions p))))) &&
        cm_expr_counts_representable p fid expr)) &&
     (!p fid first second.
       cm_stmt_counts_representable (p:cm_program) (fid:int)
         (CMSeqS (first:cm_stmt) (second:cm_stmt)) =
       (cm_i32_code_count
          (cm_stmt_code_count p fid (CMSeqS first second)) &&
        cm_stmt_counts_representable p fid first &&
        cm_stmt_counts_representable p fid second)) &&
     (!p fid body.
       cm_stmt_counts_representable (p:cm_program) (fid:int)
         (CMBlockS (body:cm_stmt)) =
       (cm_i32_code_count
          (cm_stmt_code_count p fid (CMBlockS body)) &&
        cm_stmt_counts_representable p fid body)) &&
     (!p fid guard yes no.
       cm_stmt_counts_representable (p:cm_program) (fid:int)
         (CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)) =
       (cm_i32_code_count
          (cm_stmt_code_count p fid (CMIfS guard yes no)) &&
        cm_expr_counts_representable p fid guard &&
        cm_stmt_counts_representable p fid yes &&
        cm_stmt_counts_representable p fid no)) &&
     (!p fid guard body.
       cm_stmt_counts_representable (p:cm_program) (fid:int)
         (CMWhileS (guard:cm_expr) (body:cm_stmt)) =
       (cm_i32_code_count
          (cm_stmt_code_count p fid (CMWhileS guard body)) &&
        cm_expr_counts_representable p fid guard &&
        cm_stmt_counts_representable p fid body)) &&
     (!p fid.
       cm_stmt_counts_representable (p:cm_program) (fid:int) CMBreakS =
       cm_i32_code_count (cm_stmt_code_count p fid CMBreakS)) &&
     (!p fid.
       cm_stmt_counts_representable (p:cm_program) (fid:int)
         CMContinueS =
       cm_i32_code_count (cm_stmt_code_count p fid CMContinueS)) &&
     (!p fid expr.
       cm_stmt_counts_representable (p:cm_program) (fid:int)
         (CMReturnS (expr:cm_expr)) =
       (cm_i32_code_count
          (cm_stmt_code_count p fid (CMReturnS expr)) &&
        cm_type_code_wf
          (cm_function_ret
            (inth fid (cm_program_functions p))) &&
        cm_expr_counts_representable p fid expr))`);
PROOF int _e_cm_stmt_counts_representable =
    cst_add_const_to_header(`cm_stmt_counts_representable`);

PROOF thm cm_param_stores_count_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_param_stores_count ([]:(cm_slot_d)list) = 0i) &&
     (!param rest.
       cm_param_stores_count
         ((param:cm_slot_d) :: (rest:(cm_slot_d)list)) =
       cm_param_stores_count rest +
       cm_char_normalize_count (cm_slot_ty param) + 5i)`);
PROOF thm cm_function_prologue_count_def = new_fun_definition(
    `cm_function_prologue_count (f:cm_function_d) : int =
       14i + cm_param_stores_count (cm_function_params f)`);
PROOF thm cm_function_code_count_def = new_fun_definition(
    `cm_function_code_count (p:cm_program) (fid:int) : int =
       (cm_function_prologue_count
          (inth fid (cm_program_functions p)) +
        cm_stmt_code_count p fid
          (cm_function_body (inth fid (cm_program_functions p))) +
        7i)`);
PROOF thm cm_functions_code_size_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid.
       cm_functions_code_size (p:cm_program)
         ([]:(cm_function_d)list) (fid:int) = 0i) &&
     (!p fn rest fid.
       cm_functions_code_size (p:cm_program)
         ((fn:cm_function_d) :: rest) (fid:int) =
         cm_function_code_count p fid +
         cm_functions_code_size p rest (fid + 1i))`);
PROOF thm cm_function_prefix_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p index.
       cm_function_prefix (p:cm_program)
         ([]:(cm_function_d)list) (index:int) = 0i) &&
     (!p fn rest index.
       cm_function_prefix (p:cm_program)
         ((fn:cm_function_d) :: rest) (index:int) =
         (if index == 0i then 0i
          else cm_function_code_count p
                 (ilength (cm_program_functions p) -
                  ilength ((fn:cm_function_d) :: rest)) +
               cm_function_prefix p rest (index - 1i)))`);
PROOF thm cm_function_pc_def = new_fun_definition(
    `cm_function_pc (p:cm_program) (fid:int) : int =
       11i +
       cm_function_prefix p (cm_program_functions p) fid`);
PROOF thm cm_model_code_length_def = new_fun_definition(
    `cm_model_code_length (p:cm_program) : int =
       11i + cm_functions_code_size p (cm_program_functions p) 0i`);
PROOF int _e_cm_function_prologue_count =
    cst_add_const_to_header(`cm_function_prologue_count`);
PROOF int _e_cm_function_code_count =
    cst_add_const_to_header(`cm_function_code_count`);
PROOF int _e_cm_function_pc =
    cst_add_const_to_header(`cm_function_pc`);
PROOF int _e_cm_model_code_length =
    cst_add_const_to_header(`cm_model_code_length`);

PROOF thm cm_param_counts_representable_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_param_counts_representable ([]:(cm_slot_d)list) = T) &&
     (!param rest.
       cm_param_counts_representable
         ((param:cm_slot_d) :: (rest:(cm_slot_d)list)) =
       (cm_i32_code_count
          (cm_param_stores_count (param :: rest)) &&
        cm_type_code_wf (cm_slot_ty param) &&
        cm_param_counts_representable rest))`);
PROOF thm cm_function_counts_representable_def = new_fun_definition(
    `cm_function_counts_representable (p:cm_program) (fid:int)
       (f:cm_function_d) : bool =
       (f == inth fid (cm_program_functions p) &&
        cm_param_counts_representable (cm_function_params f) &&
        cm_i32_code_count (cm_function_prologue_count f) &&
        cm_stmt_counts_representable p fid (cm_function_body f) &&
        cm_i32_code_count (cm_function_code_count p fid))`);
PROOF thm cm_functions_counts_representable_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid.
       cm_functions_counts_representable (p:cm_program)
         ([]:(cm_function_d)list) (fid:int) = T) &&
     (!p fn rest fid.
       cm_functions_counts_representable (p:cm_program)
         ((fn:cm_function_d) :: (rest:(cm_function_d)list)) (fid:int) =
       (cm_i32_code_count
          (cm_functions_code_size p (fn :: rest) fid) &&
        cm_function_counts_representable p fid fn &&
        cm_functions_counts_representable p rest (fid + 1i)))`);
PROOF thm cm_function_pcs_representable_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid.
       cm_function_pcs_representable (p:cm_program)
         ([]:(cm_function_d)list) (fid:int) =
       cm_i32_code_count (cm_function_pc p fid)) &&
     (!p fn rest fid.
       cm_function_pcs_representable (p:cm_program)
         ((fn:cm_function_d) :: (rest:(cm_function_d)list)) (fid:int) =
       (cm_i32_code_count (cm_function_pc p fid) &&
        cm_function_pcs_representable p rest (fid + 1i)))`);
PROOF int _e_cm_param_counts_representable =
    cst_add_const_to_header(`cm_param_counts_representable`);
PROOF int _e_cm_function_counts_representable =
    cst_add_const_to_header(`cm_function_counts_representable`);
PROOF int _e_cm_functions_counts_representable =
    cst_add_const_to_header(`cm_functions_counts_representable`);
PROOF int _e_cm_function_pcs_representable =
    cst_add_const_to_header(`cm_function_pcs_representable`);

PROOF thm cm_max_function_arity_from_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_max_function_arity_from ([]:(cm_function_d)list) = 0i) &&
     (!fn rest.
       cm_max_function_arity_from
         ((fn:cm_function_d) :: rest) =
       cm_imax (ilength (cm_function_params fn))
         (cm_max_function_arity_from rest))`);
PROOF thm cm_max_function_arity_def = new_fun_definition(
    `cm_max_function_arity (p:cm_program) : int =
       cm_max_function_arity_from (cm_program_functions p)`);
PROOF thm cm_stack_bound_model_def = new_fun_definition(
    `cm_stack_bound_model (p:cm_program) : int =
       3i + cm_max_function_arity p`);
PROOF int _e_cm_max_function_arity =
    cst_add_const_to_header(`cm_max_function_arity`);
PROOF int _e_cm_stack_bound_model =
    cst_add_const_to_header(`cm_stack_bound_model`);

PROOF indtype cm_emit_pair_ty = new_datatype_definition(
    "cm_emit_pair = CMEmitPair (tvm_inst)list (tvm_inst)list");
PROOF static int _t_cm_emit_pair =
    cst_add_type_to_header("cm_emit_pair", 0);
PROOF static int _c_CMEmitPair = cst_add_const_to_header(
    `CMEmitPair:(tvm_inst)list->(tvm_inst)list->cm_emit_pair`);
PROOF thm cm_lcode_of_def = new_rec_definition(
    cm_emit_pair_ty.rec,
    `cm_lcode_of
       (CMEmitPair (lcode:(tvm_inst)list) (rcode:(tvm_inst)list)) =
       lcode`);
PROOF thm cm_rcode_of_def = new_rec_definition(
    cm_emit_pair_ty.rec,
    `cm_rcode_of
       (CMEmitPair (lcode:(tvm_inst)list) (rcode:(tvm_inst)list)) =
       rcode`);

PROOF thm cm_push_code_def = new_fun_definition(
    `cm_push_code (immv:int) : (tvm_inst)list =
       [TVMInst TVMPushOp immv]`);
PROOF thm cm_const_immediate_def = new_fun_definition(
    `cm_const_immediate (ty:cm_type) (n:int) : int =
       (if ty == CMCharTy then tower_u8 n else n)`);
PROOF static int _e_cm_const_immediate =
    cst_add_const_to_header(`cm_const_immediate`);
PROOF thm cm_char_normalize_code_def = new_fun_definition(
    `cm_char_normalize_code (ty:cm_type) : (tvm_inst)list =
       (if ty == CMCharTy
        then [TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
              TVMInst TVMPushOp 256i; TVMInst TVMAddOp 0i;
              TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i]
        else [])`);
PROOF thm cm_load_code_def = new_fun_definition(
    `cm_load_code (ty:cm_type) : (tvm_inst)list =
       [TVMInst (if ty == CMCharTy then TVMLoadBOp else TVMLoadOp) 0i]`);
PROOF thm cm_store_code_def = new_fun_definition(
    `cm_store_code (ty:cm_type) : (tvm_inst)list =
       [TVMInst (if ty == CMCharTy then TVMStoreBOp else TVMStoreOp) 0i]`);

PROOF thm cm_param_offset_def = new_fun_definition(
    `cm_param_offset (p:cm_program) (fid:int) (slot:int) : int =
       8i + cm_slots_prefix (cm_program_structs p)
         (cm_function_params
           (inth fid (cm_program_functions p))) slot`);
PROOF thm cm_local_offset_def = new_fun_definition(
    `cm_local_offset (p:cm_program) (fid:int) (slot:int) : int =
       8i +
       cm_slots_size (cm_program_structs p)
         (cm_function_params
           (inth fid (cm_program_functions p))) +
       cm_slots_prefix (cm_program_structs p)
         (cm_function_locals
           (inth fid (cm_program_functions p))) slot`);
PROOF thm cm_temp_offset_def = new_fun_definition(
    `cm_temp_offset (p:cm_program) (fid:int) (temp:int) : int =
       8i +
       cm_slots_size (cm_program_structs p)
         (cm_function_params
           (inth fid (cm_program_functions p))) +
       cm_slots_size (cm_program_structs p)
         (cm_function_locals
           (inth fid (cm_program_functions p))) +
       8i * temp`);
PROOF thm cm_fp_relative_address_code_def = new_fun_definition(
    `cm_fp_relative_address_code (offset:int) : (tvm_inst)list =
       [TVMInst TVMPushOp 8i; TVMInst TVMLoadOp 0i;
        TVMInst TVMPushOp offset; TVMInst TVMAddOp 0i]`);
PROOF thm cm_binding_address_code_def = new_fun_definition(
    `cm_binding_address_code (p:cm_program) (fid:int)
       (scope:int) (slot:int) : (tvm_inst)list =
       (if scope == 0i
        then cm_push_code (cm_global_address p slot)
        else cm_fp_relative_address_code
          (if scope == 1i then cm_local_offset p fid slot
           else cm_param_offset p fid slot))`);
PROOF thm cm_temp_store_code_def = new_fun_definition(
    `cm_temp_store_code (p:cm_program) (fid:int)
       (temp:int) : (tvm_inst)list =
       cm_fp_relative_address_code (cm_temp_offset p fid temp) ++
       [TVMInst TVMStoreOp 0i]`);
PROOF thm cm_temp_load_code_def = new_fun_definition(
    `cm_temp_load_code (p:cm_program) (fid:int)
       (temp:int) : (tvm_inst)list =
       cm_fp_relative_address_code (cm_temp_offset p fid temp) ++
       [TVMInst TVMLoadOp 0i]`);

PROOF thm cm_binary_opcode_def = new_fun_definition(
    `cm_binary_opcode (op:int) : tvm_opcode =
       (if op == 2i then TVMEqOp
        else if op == 3i then TVMNeOp
        else if op == 4i then TVMLtOp
        else if op == 5i then TVMLeOp
        else if op == 6i then TVMGtOp
        else if op == 7i then TVMGeOp
        else if op == 8i then TVMAddOp
        else if op == 9i then TVMSubOp
        else if op == 10i then TVMMulOp
        else if op == 11i then TVMDivOp
        else TVMModOp)`);
PROOF thm cm_pointer_scale_def = new_fun_definition(
    `cm_pointer_scale (p:cm_program) (expr:cm_expr) : int =
       cm_type_size (cm_program_structs p)
         (cm_pointee (cm_expr_type expr))`);
PROOF thm cm_binary_finish_code_def = new_fun_definition(
    `cm_binary_finish_code (p:cm_program) (fid:int)
       (op:int) (left:cm_expr) (right:cm_expr)
       (temp:int) : (tvm_inst)list =
       (cm_temp_load_code p fid temp ++
        (if op == 8i && cm_is_pointer (cm_expr_type right)
         then [TVMInst TVMPushOp (cm_pointer_scale p right);
               TVMInst TVMMulOp 0i; TVMInst TVMSwapOp 0i;
               TVMInst TVMAddOp 0i]
         else [TVMInst TVMSwapOp 0i] ++
           (if op == 8i && cm_is_pointer (cm_expr_type left)
            then [TVMInst TVMPushOp (cm_pointer_scale p left);
                  TVMInst TVMMulOp 0i; TVMInst TVMAddOp 0i]
            else if op == 9i &&
                    cm_is_pointer (cm_expr_type left) &&
                    cm_is_pointer (cm_expr_type right)
            then [TVMInst TVMSubOp 0i;
                  TVMInst TVMPushOp (cm_pointer_scale p left);
                  TVMInst TVMDivOp 0i]
            else if op == 9i &&
                    cm_is_pointer (cm_expr_type left)
            then [TVMInst TVMPushOp (cm_pointer_scale p left);
                  TVMInst TVMMulOp 0i; TVMInst TVMSubOp 0i]
            else [TVMInst (cm_binary_opcode op) 0i])))`);
PROOF thm cm_return_epilogue_def = new_fun_definition(
    `cm_return_epilogue : (tvm_inst)list =
       [TVMInst TVMPushOp 8i; TVMInst TVMLoadOp 0i;
        TVMInst TVMLoadOp 0i; TVMInst TVMPushOp 8i;
        TVMInst TVMStoreOp 0i; TVMInst TVMRetOp 0i]`);

PROOF thm cm_emit_args_reload_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid slot.
       cm_emit_args_reload (p:cm_program) (fid:int) (slot:int)
         ([]:(cm_expr)list) = []) &&
     (!p fid slot arg args.
       cm_emit_args_reload (p:cm_program) (fid:int) (slot:int)
         ((arg:cm_expr) :: (args:(cm_expr)list)) =
         cm_temp_load_code p fid slot ++
         cm_emit_args_reload p fid (slot + 1i) args)`);
PROOF thm cm_emit_expr_pair_def = new_rec_definition(
    get_cm_expr_recursion(),
    `(!p fid pc temp n ty.
       cm_emit_expr_pair (p:cm_program) (fid:int) (pc:int) (temp:int)
         (CMConstE (n:int) (ty:cm_type)) =
         CMEmitPair []
           (cm_push_code (cm_const_immediate ty n))) &&
     (!p fid pc temp sid ty.
       cm_emit_expr_pair (p:cm_program) (fid:int) (pc:int) (temp:int)
         (CMStringE (sid:int) (ty:cm_type)) =
         CMEmitPair [] (cm_push_code (cm_string_address p sid))) &&
     (!p fid pc temp scope slot ty.
       cm_emit_expr_pair (p:cm_program) (fid:int) (pc:int) (temp:int)
         (CMVarE (scope:int) (slot:int) (ty:cm_type)) =
         CMEmitPair
           (cm_binding_address_code p fid scope slot)
           (cm_binding_address_code p fid scope slot ++
            (if cm_binding_array p fid scope slot
             then [] else cm_load_code ty))) &&
     (!p fid pc temp dst src ty.
       cm_emit_expr_pair (p:cm_program) (fid:int) (pc:int) (temp:int)
         (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) =
         CMEmitPair []
           (cm_lcode_of (cm_emit_expr_pair p fid pc temp dst) ++
            cm_temp_store_code p fid temp ++
            cm_rcode_of (cm_emit_expr_pair p fid
              (pc + cm_lvalue_code_count p fid dst + 5i)
              (temp + 1i) src) ++
            cm_char_normalize_code ty ++
            cm_temp_load_code p fid temp ++
            cm_store_code ty ++
            cm_temp_load_code p fid temp ++
            cm_load_code ty)) &&
     (!p fid pc temp op left right ty.
       cm_emit_expr_pair (p:cm_program) (fid:int) (pc:int) (temp:int)
         (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
           (ty:cm_type)) =
         CMEmitPair []
           (if op == 0i || op == 1i
            then cm_rcode_of
                   (cm_emit_expr_pair p fid pc temp left) ++
                 [TVMInst (if op == 0i then TVMJnzOp else TVMJzOp)
                    (pc + cm_rvalue_code_count p fid left +
                     cm_rvalue_code_count p fid right + 4i)] ++
                 cm_rcode_of (cm_emit_expr_pair p fid
                   (pc + cm_rvalue_code_count p fid left + 1i)
                   temp right) ++
                 [TVMInst TVMPushOp 0i; TVMInst TVMNeOp 0i;
                  TVMInst TVMJmpOp
                    (pc + cm_rvalue_code_count p fid left +
                     cm_rvalue_code_count p fid right + 5i);
                  TVMInst TVMPushOp (if op == 0i then 1i else 0i)]
            else cm_rcode_of
                   (cm_emit_expr_pair p fid pc temp left) ++
                 cm_temp_store_code p fid temp ++
                 cm_rcode_of (cm_emit_expr_pair p fid
                   (pc + cm_rvalue_code_count p fid left + 5i)
                   (temp + 1i) right) ++
                 cm_binary_finish_code p fid op left right temp)) &&
     (!p fid pc temp op arg ty.
       cm_emit_expr_pair (p:cm_program) (fid:int) (pc:int) (temp:int)
         (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) =
         (if op == 2i
          then CMEmitPair
            (cm_rcode_of (cm_emit_expr_pair p fid pc temp arg))
            (cm_rcode_of (cm_emit_expr_pair p fid pc temp arg) ++
             cm_load_code ty)
          else if op == 3i
          then CMEmitPair []
            (cm_lcode_of (cm_emit_expr_pair p fid pc temp arg))
          else CMEmitPair []
            (cm_rcode_of (cm_emit_expr_pair p fid pc temp arg) ++
             [TVMInst TVMPushOp (if op == 0i then --1i else 0i);
              TVMInst (if op == 0i then TVMMulOp else TVMEqOp) 0i]))) &&
     (!p fid pc temp base index ty.
       cm_emit_expr_pair (p:cm_program) (fid:int) (pc:int) (temp:int)
         (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) =
         CMEmitPair
           (cm_rcode_of (cm_emit_expr_pair p fid pc temp base) ++
            cm_temp_store_code p fid temp ++
            cm_rcode_of (cm_emit_expr_pair p fid
              (pc + cm_rvalue_code_count p fid base + 5i)
              (temp + 1i) index) ++
            [TVMInst TVMPushOp
               (cm_type_size (cm_program_structs p) ty);
             TVMInst TVMMulOp 0i] ++
            cm_temp_load_code p fid temp ++
            [TVMInst TVMAddOp 0i])
           (cm_rcode_of (cm_emit_expr_pair p fid pc temp base) ++
            cm_temp_store_code p fid temp ++
            cm_rcode_of (cm_emit_expr_pair p fid
              (pc + cm_rvalue_code_count p fid base + 5i)
              (temp + 1i) index) ++
            [TVMInst TVMPushOp
               (cm_type_size (cm_program_structs p) ty);
             TVMInst TVMMulOp 0i] ++
            cm_temp_load_code p fid temp ++
            [TVMInst TVMAddOp 0i] ++ cm_load_code ty)) &&
     (!p fid pc temp base mid ty.
       cm_emit_expr_pair (p:cm_program) (fid:int) (pc:int) (temp:int)
         (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) =
         CMEmitPair
           (cm_rcode_of (cm_emit_expr_pair p fid pc temp base) ++
            [TVMInst TVMPushOp
               (cm_member_offset (cm_program_structs p)
                 (cm_struct_id (cm_pointee (cm_expr_type base))) mid);
             TVMInst TVMAddOp 0i])
           (cm_rcode_of (cm_emit_expr_pair p fid pc temp base) ++
            [TVMInst TVMPushOp
               (cm_member_offset (cm_program_structs p)
                 (cm_struct_id (cm_pointee (cm_expr_type base))) mid);
             TVMInst TVMAddOp 0i] ++
            (if cm_member_array p (cm_expr_type base) mid
             then [] else cm_load_code ty))) &&
     (!p fid pc temp callee args ty.
       cm_emit_expr_pair (p:cm_program) (fid:int) (pc:int) (temp:int)
         (CMCallE (callee:int) (args:(cm_expr)list) (ty:cm_type)) =
         CMEmitPair []
           (cm_emit_args_store p fid pc temp
              (temp + ilength args) args ++
            cm_emit_args_reload p fid temp args ++
            [TVMInst TVMCallOp (cm_function_pc p callee)])) &&
     (!p fid pc temp asked ty.
       cm_emit_expr_pair (p:cm_program) (fid:int) (pc:int) (temp:int)
         (CMSizeofE (asked:cm_type) (ty:cm_type)) =
         CMEmitPair []
           (cm_push_code (cm_type_size (cm_program_structs p) asked))) &&
     (!p fid pc temp ty.
       cm_emit_expr_pair (p:cm_program) (fid:int) (pc:int) (temp:int)
         (CMGetcE (ty:cm_type)) =
         CMEmitPair [] [TVMInst TVMGetcOp 0i]) &&
     (!p fid pc temp arg ty.
       cm_emit_expr_pair (p:cm_program) (fid:int) (pc:int) (temp:int)
         (CMPutcE (arg:cm_expr) (ty:cm_type)) =
         CMEmitPair []
           (cm_rcode_of (cm_emit_expr_pair p fid pc temp arg) ++
            [TVMInst TVMDupOp 0i; TVMInst TVMPutcOp 0i])) &&
     (!p fid pc temp arg ty.
       cm_emit_expr_pair (p:cm_program) (fid:int) (pc:int) (temp:int)
         (CMPutiE (arg:cm_expr) (ty:cm_type)) =
         CMEmitPair []
           (cm_rcode_of (cm_emit_expr_pair p fid pc temp arg) ++
            [TVMInst TVMDupOp 0i; TVMInst TVMPutiOp 0i])) &&
     (!p fid pc temp arg ty.
       cm_emit_expr_pair (p:cm_program) (fid:int) (pc:int) (temp:int)
         (CMExitE (arg:cm_expr) (ty:cm_type)) =
         CMEmitPair []
           (cm_rcode_of (cm_emit_expr_pair p fid pc temp arg) ++
            cm_char_normalize_code CMCharTy ++
            [TVMInst TVMHaltOp 0i])) &&
     (!p fid pc slot scratch.
       cm_emit_args_store (p:cm_program) (fid:int) (pc:int)
         (slot:int) (scratch:int) ([]:(cm_expr)list) = []) &&
     (!p fid pc slot scratch arg args.
       cm_emit_args_store (p:cm_program) (fid:int) (pc:int)
         (slot:int) (scratch:int)
         ((arg:cm_expr) :: (args:(cm_expr)list)) =
         cm_rcode_of (cm_emit_expr_pair p fid pc scratch arg) ++
         cm_temp_store_code p fid slot ++
         cm_emit_args_store p fid
           (pc + cm_rvalue_code_count p fid arg + 5i)
           (slot + 1i) scratch args)`);
PROOF int _e_cm_emit_expr_pair =
    cst_add_const_to_header(`cm_emit_expr_pair`);
PROOF int _e_cm_emit_args_store =
    cst_add_const_to_header(`cm_emit_args_store`);


PROOF thm cm_emit_lvalue_def = new_fun_definition(
    `cm_emit_lvalue (p:cm_program) (fid:int) (pc:int) (temp:int)
       (expr:cm_expr) : (tvm_inst)list =
       cm_lcode_of (cm_emit_expr_pair p fid pc temp expr)`);
PROOF thm cm_emit_rvalue_def = new_fun_definition(
    `cm_emit_rvalue (p:cm_program) (fid:int) (pc:int) (temp:int)
       (expr:cm_expr) : (tvm_inst)list =
       cm_rcode_of (cm_emit_expr_pair p fid pc temp expr)`);
PROOF int _e_cm_emit_lvalue =
    cst_add_const_to_header(`cm_emit_lvalue`);
PROOF int _e_cm_emit_rvalue =
    cst_add_const_to_header(`cm_emit_rvalue`);

PROOF thm cm_emit_stmt_def = new_rec_definition(
    get_cm_stmt_recursion(),
    `(!p fid pc temp breakpc continuepc.
       cm_emit_stmt (p:cm_program) (fid:int) (pc:int) (temp:int)
         (breakpc:int) (continuepc:int) CMSkipS = []) &&
     (!p fid pc temp breakpc continuepc expr.
       cm_emit_stmt (p:cm_program) (fid:int) (pc:int) (temp:int)
         (breakpc:int) (continuepc:int) (CMExprS (expr:cm_expr)) =
         cm_emit_rvalue p fid pc temp expr ++
         [TVMInst TVMPopOp 0i]) &&
     (!p fid pc temp breakpc continuepc slot.
       cm_emit_stmt (p:cm_program) (fid:int) (pc:int) (temp:int)
         (breakpc:int) (continuepc:int) (CMDeclS (slot:int)) = []) &&
     (!p fid pc temp breakpc continuepc slot expr.
       cm_emit_stmt (p:cm_program) (fid:int) (pc:int) (temp:int)
         (breakpc:int) (continuepc:int)
         (CMInitS (slot:int) (expr:cm_expr)) =
         cm_emit_rvalue p fid pc temp expr ++
         cm_char_normalize_code
           (cm_slot_ty
             (inth slot (cm_function_locals
               (inth fid (cm_program_functions p))))) ++
         cm_fp_relative_address_code (cm_local_offset p fid slot) ++
         cm_store_code
           (cm_slot_ty
             (inth slot (cm_function_locals
               (inth fid (cm_program_functions p)))))) &&
     (!p fid pc temp breakpc continuepc first second.
       cm_emit_stmt (p:cm_program) (fid:int) (pc:int) (temp:int)
         (breakpc:int) (continuepc:int)
         (CMSeqS (first:cm_stmt) (second:cm_stmt)) =
         cm_emit_stmt p fid pc temp breakpc continuepc first ++
         cm_emit_stmt p fid
           (pc + cm_stmt_code_count p fid first)
           temp breakpc continuepc second) &&
     (!p fid pc temp breakpc continuepc body.
       cm_emit_stmt (p:cm_program) (fid:int) (pc:int) (temp:int)
         (breakpc:int) (continuepc:int) (CMBlockS (body:cm_stmt)) =
         cm_emit_stmt p fid pc temp breakpc continuepc body) &&
     (!p fid pc temp breakpc continuepc guard yes no.
       cm_emit_stmt (p:cm_program) (fid:int) (pc:int) (temp:int)
         (breakpc:int) (continuepc:int)
         (CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)) =
         cm_emit_rvalue p fid pc temp guard ++
         [TVMInst TVMJzOp
           (pc + cm_rvalue_code_count p fid guard + 1i +
            cm_stmt_code_count p fid yes + 1i)] ++
         cm_emit_stmt p fid
           (pc + cm_rvalue_code_count p fid guard + 1i)
           temp breakpc continuepc yes ++
         [TVMInst TVMJmpOp
           (pc + cm_stmt_code_count p fid
             (CMIfS guard yes no))] ++
         cm_emit_stmt p fid
           (pc + cm_rvalue_code_count p fid guard + 1i +
            cm_stmt_code_count p fid yes + 1i)
           temp breakpc continuepc no) &&
     (!p fid pc temp breakpc continuepc guard body.
       cm_emit_stmt (p:cm_program) (fid:int) (pc:int) (temp:int)
         (breakpc:int) (continuepc:int)
         (CMWhileS (guard:cm_expr) (body:cm_stmt)) =
         cm_emit_rvalue p fid pc temp guard ++
         [TVMInst TVMJzOp
           (pc + cm_stmt_code_count p fid
             (CMWhileS guard body))] ++
         cm_emit_stmt p fid
           (pc + cm_rvalue_code_count p fid guard + 1i)
           temp
           (pc + cm_stmt_code_count p fid (CMWhileS guard body))
           pc body ++
         [TVMInst TVMJmpOp pc]) &&
     (!p fid pc temp breakpc continuepc.
       cm_emit_stmt (p:cm_program) (fid:int) (pc:int) (temp:int)
         (breakpc:int) (continuepc:int) CMBreakS =
         [TVMInst TVMJmpOp breakpc]) &&
     (!p fid pc temp breakpc continuepc.
       cm_emit_stmt (p:cm_program) (fid:int) (pc:int) (temp:int)
         (breakpc:int) (continuepc:int) CMContinueS =
         [TVMInst TVMJmpOp continuepc]) &&
     (!p fid pc temp breakpc continuepc expr.
       cm_emit_stmt (p:cm_program) (fid:int) (pc:int) (temp:int)
         (breakpc:int) (continuepc:int) (CMReturnS (expr:cm_expr)) =
         cm_emit_rvalue p fid pc temp expr ++
         cm_char_normalize_code
           (cm_function_ret
             (inth fid (cm_program_functions p))) ++
         cm_return_epilogue)`);
PROOF int _e_cm_emit_stmt =
    cst_add_const_to_header(`cm_emit_stmt`);

PROOF thm cm_emit_param_stores_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid slot.
       cm_emit_param_stores (p:cm_program) (fid:int) (slot:int)
         ([]:(cm_slot_d)list) = []) &&
     (!p fid slot param rest.
       cm_emit_param_stores (p:cm_program) (fid:int) (slot:int)
         ((param:cm_slot_d) :: (rest:(cm_slot_d)list)) =
         cm_emit_param_stores p fid (slot + 1i) rest ++
         cm_char_normalize_code (cm_slot_ty param) ++
         cm_fp_relative_address_code
           (cm_param_offset p fid slot) ++
         cm_store_code (cm_slot_ty param))`);
PROOF thm cm_emit_prologue_def = new_fun_definition(
    `cm_emit_prologue (p:cm_program) (fid:int) : (tvm_inst)list =
       [TVMInst TVMPushOp 8i; TVMInst TVMLoadOp 0i;
        TVMInst TVMDupOp 0i;
        TVMInst TVMPushOp
          (cm_frame_size (cm_program_structs p)
            (inth fid (cm_program_functions p)));
        TVMInst TVMSubOp 0i; TVMInst TVMStoreOp 0i;
        TVMInst TVMPushOp 8i; TVMInst TVMLoadOp 0i;
        TVMInst TVMPushOp
          (cm_frame_size (cm_program_structs p)
            (inth fid (cm_program_functions p)));
        TVMInst TVMSubOp 0i; TVMInst TVMDupOp 0i;
        TVMInst TVMPushOp 8i; TVMInst TVMStoreOp 0i;
        TVMInst TVMPopOp 0i] ++
       cm_emit_param_stores p fid 0i
         (cm_function_params
           (inth fid (cm_program_functions p)))`);
PROOF thm cm_emit_function_def = new_fun_definition(
    `cm_emit_function (p:cm_program) (fid:int) : (tvm_inst)list =
       cm_emit_prologue p fid ++
       cm_emit_stmt p fid
         (cm_function_pc p fid +
          cm_function_prologue_count
            (inth fid (cm_program_functions p)))
         0i 0i 0i
         (cm_function_body
           (inth fid (cm_program_functions p))) ++
       [TVMInst TVMPushOp 0i] ++ cm_return_epilogue`);
PROOF thm cm_emit_functions_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid.
       cm_emit_functions (p:cm_program) (fid:int)
         ([]:(cm_function_d)list) = []) &&
     (!p fid fn rest.
       cm_emit_functions (p:cm_program) (fid:int)
         ((fn:cm_function_d) :: (rest:(cm_function_d)list)) =
         cm_emit_function p fid ++
         cm_emit_functions p (fid + 1i) rest)`);

PROOF thm cm_emit_prelude_def = new_fun_definition(
    `cm_emit_prelude (p:cm_program) : (tvm_inst)list =
       [TVMInst TVMPushOp 1048576i;
        TVMInst TVMPushOp 8i; TVMInst TVMStoreOp 0i;
        TVMInst TVMCallOp (cm_function_pc p (cm_program_main p));
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMAddOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMHaltOp 0i]`);
PROOF thm cm_model_code_def = new_fun_definition(
    `cm_model_code (p:cm_program) : (tvm_inst)list =
       cm_emit_prelude p ++
       cm_emit_functions p 0i (cm_program_functions p)`);
PROOF int _e_cm_model_code =
    cst_add_const_to_header(`cm_model_code`);

PROOF thm cm_global_init_bytes_def = new_fun_definition(
    `cm_global_init_bytes (g:cm_global_d) : (int)list =
       (if cm_global_ty g == CMCharTy
        then [tower_u8 (cm_global_init g)]
        else tower_word_bytes (cm_global_init g))`);
PROOF thm cm_global_bytes_def = new_fun_definition(
    `cm_global_bytes (structs:(cm_struct_d)list)
       (g:cm_global_d) : (int)list =
       (let size = cm_global_size structs g in
        let initial = cm_global_init_bytes g in
        if 0i <= size
        then if cm_global_has_init g && ilength initial <= size
             then initial ++ ireplicate (size - ilength initial) 0i
             else ireplicate size 0i
        else [])`);
PROOF thm cm_global_model_size_def = new_fun_definition(
    `cm_global_model_size (structs:(cm_struct_d)list)
       (g:cm_global_d) : int =
       (if 0i <= cm_global_size structs g
        then cm_global_size structs g else 0i)`);
PROOF thm cm_globals_model_size_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!structs.
       cm_globals_model_size (structs:(cm_struct_d)list)
         ([]:(cm_global_d)list) = 0i) &&
     (!structs g rest.
       cm_globals_model_size (structs:(cm_struct_d)list)
         ((g:cm_global_d) :: (rest:(cm_global_d)list)) =
       cm_global_model_size structs g +
       cm_globals_model_size structs rest)`);
PROOF thm cm_model_data_size_count_def = new_fun_definition(
    `cm_model_data_size_count (p:cm_program) : int =
       8i +
       cm_globals_model_size (cm_program_structs p)
         (cm_program_globals p) +
       cm_strings_size (cm_program_strings p)`);
PROOF thm cm_globals_bytes_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!structs.
       cm_globals_bytes (structs:(cm_struct_d)list)
         ([]:(cm_global_d)list) = []) &&
     (!structs g rest.
       cm_globals_bytes (structs:(cm_struct_d)list)
         ((g:cm_global_d) :: (rest:(cm_global_d)list)) =
         cm_global_bytes structs g ++
         cm_globals_bytes structs rest)`);
PROOF thm cm_strings_bytes_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_strings_bytes ([]:(cm_string_d)list) = []) &&
     (!s rest.
       cm_strings_bytes
         ((s:cm_string_d) :: (rest:(cm_string_d)list)) =
         cm_string_bytes s ++ [0i] ++ cm_strings_bytes rest)`);
PROOF thm cm_model_data_bytes_def = new_fun_definition(
    `cm_model_data_bytes (p:cm_program) : (int)list =
       ireplicate 8i 0i ++
       cm_globals_bytes (cm_program_structs p)
         (cm_program_globals p) ++
       cm_strings_bytes (cm_program_strings p)`);
PROOF thm cm_bytes_patches_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!addr.
       cm_bytes_patches ([]:(int)list) (addr:int) = []) &&
     (!byte rest addr.
       cm_bytes_patches
         ((byte:int) :: (rest:(int)list)) (addr:int) =
         TVMPatch addr byte ::
         cm_bytes_patches rest (addr + 1i))`);
PROOF thm cm_model_patches_def = new_fun_definition(
    `cm_model_patches (p:cm_program) : (tvm_patch)list =
       cm_bytes_patches (cm_model_data_bytes p) 8i`);
PROOF thm cm_compile_model_def = new_fun_definition(
    `cm_compile_model (p:cm_program) : tvm_object =
       TVMObject 0i (cm_model_code p) (cm_model_patches p)`);
PROOF thm cm_model_data_length_def = new_fun_definition(
    `cm_model_data_length (p:cm_program) : int =
       ilength (cm_model_data_bytes p)`);
PROOF int _e_cm_global_init_bytes =
    cst_add_const_to_header(`cm_global_init_bytes`);
PROOF int _e_cm_global_bytes =
    cst_add_const_to_header(`cm_global_bytes`);
PROOF int _e_cm_global_model_size =
    cst_add_const_to_header(`cm_global_model_size`);
PROOF int _e_cm_globals_model_size =
    cst_add_const_to_header(`cm_globals_model_size`);
PROOF int _e_cm_model_data_size_count =
    cst_add_const_to_header(`cm_model_data_size_count`);
PROOF int _e_cm_globals_bytes =
    cst_add_const_to_header(`cm_globals_bytes`);
PROOF int _e_cm_strings_bytes =
    cst_add_const_to_header(`cm_strings_bytes`);
PROOF int _e_cm_model_data_bytes =
    cst_add_const_to_header(`cm_model_data_bytes`);
PROOF int _e_cm_compile_model =
    cst_add_const_to_header(`cm_compile_model`);
PROOF int _e_cm_model_data_length =
    cst_add_const_to_header(`cm_model_data_length`);


PROOF thm cm_stack_height_max_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_stack_height_max ([]:(int)list) = 0i) &&
     (!height rest.
       cm_stack_height_max
         ((height:int) :: (rest:(int)list)) =
       cm_imax height (cm_stack_height_max rest))`);
PROOF thm cm_stack_at_def = new_fun_definition(
    `cm_stack_at (code:(tvm_inst)list) (heights:(int)list)
       (pc:int) (height:int) : bool =
       (inth pc heights == height)`);
PROOF thm cm_stack_head_ok_def = new_fun_definition(
    `cm_stack_head_ok (code:(tvm_inst)list)
       (heights:(int)list) (pc:int) (inst:tvm_inst)
       (height:int) : bool =
       (let op = tvm_inst_op inst in
        let imm = tvm_inst_imm inst in
        if op == TVMPushOp
        then cm_stack_at code heights (pc + 1i) (height + 1i)
        else if op == TVMPopOp
        then 1i <= height &&
             cm_stack_at code heights (pc + 1i) (height - 1i)
        else if op == TVMDupOp
        then 1i <= height &&
             cm_stack_at code heights (pc + 1i) (height + 1i)
        else if op == TVMSwapOp
        then 2i <= height &&
             cm_stack_at code heights (pc + 1i) height
        else if op == TVMLoadOp || op == TVMLoadBOp
        then 1i <= height &&
             cm_stack_at code heights (pc + 1i) height
        else if op == TVMStoreOp || op == TVMStoreBOp
        then 2i <= height &&
             cm_stack_at code heights (pc + 1i) (height - 2i)
        else if op == TVMAddOp || op == TVMSubOp ||
                op == TVMMulOp || op == TVMDivOp ||
                op == TVMModOp || op == TVMEqOp ||
                op == TVMNeOp || op == TVMLtOp ||
                op == TVMLeOp || op == TVMGtOp ||
                op == TVMGeOp
        then 2i <= height &&
             cm_stack_at code heights (pc + 1i) (height - 1i)
        else if op == TVMJmpOp
        then cm_stack_at code heights imm height
        else if op == TVMJzOp || op == TVMJnzOp
        then 1i <= height &&
             cm_stack_at code heights imm (height - 1i) &&
             cm_stack_at code heights (pc + 1i) (height - 1i)
        else if op == TVMCallOp
        then cm_stack_at code heights imm height &&
             cm_stack_at code heights (pc + 1i) 1i
        else if op == TVMRetOp
        then height == 1i
        else if op == TVMGetcOp
        then cm_stack_at code heights (pc + 1i) (height + 1i)
        else if op == TVMPutcOp || op == TVMPutiOp
        then 1i <= height &&
             cm_stack_at code heights (pc + 1i) (height - 1i)
        else height == 1i)`);
PROOF thm cm_stack_edges_from_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!code heights pc annotations.
       cm_stack_edges_from (code:(tvm_inst)list)
         (heights:(int)list) (pc:int) ([]:(tvm_inst)list)
         (annotations:(int)list) =
       (annotations == [])) &&
     (!code heights pc inst rest annotations.
       cm_stack_edges_from code heights pc
         ((inst:tvm_inst) :: (rest:(tvm_inst)list))
         (annotations:(int)list) =
       (~(annotations == []) &&
        0i <= HD annotations &&
        cm_stack_head_ok code heights pc inst
          (HD annotations) &&
        cm_stack_edges_from code heights (pc + 1i)
          rest (TL annotations)))`);
PROOF thm cm_stack_call_insts_from_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!obj heights entries arities pc annotations.
       cm_stack_call_insts_from (obj:tvm_object)
         (heights:(int)list) (entries:(int)list)
         (arities:(int)list) (pc:int) ([]:(tvm_inst)list)
         (annotations:(int)list) = T) &&
     (!obj heights entries arities pc inst rest annotations.
       cm_stack_call_insts_from obj heights entries arities pc
         ((inst:tvm_inst) :: (rest:(tvm_inst)list))
         (annotations:(int)list) =
       (~(annotations == []) &&
        (tvm_inst_op inst == TVMCallOp ==>
         ?fid.
           0i <= fid && fid < ilength entries &&
           tvm_inst_imm inst == inth fid entries &&
           HD annotations == inth fid arities) &&
        cm_stack_call_insts_from obj heights entries arities
          (pc + 1i) rest (TL annotations)))`);
PROOF thm cm_stack_call_sites_def = new_fun_definition(
    `cm_stack_call_sites (obj:tvm_object)
       (heights:(int)list) (entries:(int)list)
       (arities:(int)list) : bool =
       (ilength entries == ilength arities &&
        (!(fid:int).
           0i <= fid ==> fid < ilength entries ==>
           inth (inth fid entries) heights == inth fid arities) &&
        cm_stack_call_insts_from obj heights entries arities 0i
          (tvm_object_code obj) heights)`);
PROOF thm cm_stack_certificate_def = new_fun_definition(
    `cm_stack_certificate (obj:tvm_object)
       (heights:(int)list) (entries:(int)list)
       (arities:(int)list) (peak:int) : bool =
       (tvm_object_wf obj &&
        ilength heights == ilength (tvm_object_code obj) &&
        inth (tvm_object_entry obj) heights == 0i &&
        cm_stack_edges_from (tvm_object_code obj) heights 0i
          (tvm_object_code obj) heights &&
        peak == cm_stack_height_max heights &&
        cm_stack_call_sites obj heights entries arities)`);
PROOF thm cm_stack_summary_def = new_fun_definition(
    `cm_stack_summary (obj:tvm_object) (bound:int) : bool =
       (?heights entries arities peak.
          cm_stack_certificate obj
            (heights:(int)list) (entries:(int)list)
            (arities:(int)list) (peak:int) &&
          peak <= bound)`);
PROOF int _e_cm_stack_summary =
    cst_add_const_to_header(`cm_stack_summary`);

PROOF thm cm_codegen_fields_representable_def = new_fun_definition(
    `cm_codegen_fields_representable (p:cm_program) : bool =
       (tvm_code_shape (cm_model_code p) &&
        tvm_targets_valid (cm_model_code p) &&
        tvm_patches_valid (cm_model_patches p) &&
        tvm_target_valid (cm_model_code p) 0i)`);
PROOF thm cm_codegen_counts_representable_def = new_fun_definition(
    `cm_codegen_counts_representable (p:cm_program) : bool =
       (cm_functions_counts_representable p
          (cm_program_functions p) 0i &&
        cm_function_pcs_representable p
          (cm_program_functions p) 0i)`);
PROOF int _e_cm_codegen_counts_representable =
    cst_add_const_to_header(`cm_codegen_counts_representable`);

PROOF thm cm_codegen_admissible_def = new_fun_definition(
    `cm_codegen_admissible (p:cm_program) : bool =
       (cm_typed_program p &&
        0i <= cm_model_code_length p &&
        cm_model_code_length p <= 2147483647i &&
        0i <= cm_model_data_length p &&
        cm_model_data_length p <= 1048568i &&
        0i <= cm_stack_bound_model p &&
        cm_stack_bound_model p <= 65536i &&
        cm_codegen_fields_representable p &&
        cm_codegen_counts_representable p)`);
PROOF int _e_cm_codegen_admissible =
    cst_add_const_to_header(`cm_codegen_admissible`);

PROOF thm cm_wf_program_def = new_fun_definition(
    `cm_wf_program (p:cm_program) : bool =
       cm_codegen_admissible p`);
PROOF int _e_cm_wf_program =
    cst_add_const_to_header(`cm_wf_program`);

PROOF static thm cm_prove_ilength_cond(void) {
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
PROOF static thm cm_ilength_cond = cm_prove_ilength_cond();
PROOF static thm cm_prove_apply_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(b:bool). !(f:A->B). !(x:A). !(y:A).
         f (if b then x else y) ==
         (if b then f x else f y)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(leaf, `b:bool`, "hb");
  for (size_t i = 0; i < 2; ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF static thm cm_apply_cond = cm_prove_apply_cond();
PROOF static thm cm_lcode_cond = beta_norm(ispecl_rule(TERM_LIST(
    `b:bool`, `cm_lcode_of:cm_emit_pair->(tvm_inst)list`,
    `x:cm_emit_pair`, `y:cm_emit_pair`), cm_apply_cond));
PROOF static thm cm_rcode_cond = beta_norm(ispecl_rule(TERM_LIST(
    `b:bool`, `cm_rcode_of:cm_emit_pair->(tvm_inst)list`,
    `x:cm_emit_pair`, `y:cm_emit_pair`), cm_apply_cond));
PROOF static thm cm_lcount_cond = beta_norm(ispecl_rule(TERM_LIST(
    `b:bool`, `cm_lcount_of:cm_code_counts->int`,
    `x:cm_code_counts`, `y:cm_code_counts`), cm_apply_cond));
PROOF static thm cm_rcount_cond = beta_norm(ispecl_rule(TERM_LIST(
    `b:bool`, `cm_rcount_of:cm_code_counts->int`,
    `x:cm_code_counts`, `y:cm_code_counts`), cm_apply_cond));



PROOF static thm cm_prove_expr_code_lengths(void) {
  gnode root = gnode_new_with_ccl(
      `(!(expr:cm_expr).
          (!(p:cm_program) fid pc temp.
             ilength
               (cm_lcode_of (cm_emit_expr_pair p fid pc temp expr)) ==
               cm_lvalue_code_count p fid expr) &&
          (!(p:cm_program) fid pc temp.
             ilength
               (cm_rcode_of (cm_emit_expr_pair p fid pc temp expr)) ==
               cm_rvalue_code_count p fid expr)) &&
       (!(args:(cm_expr)list). !p fid pc slot scratch.
          ilength (cm_emit_args_store p fid pc slot scratch args) +
          ilength (cm_emit_args_reload p fid slot args) + 1i ==
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
            cm_emit_expr_pair_def,
            cm_lcode_of_def, cm_rcode_of_def,
            cm_lvalue_code_count_def, cm_rvalue_code_count_def,
            cm_expr_code_counts_def,
            cm_lcount_of_def, cm_rcount_of_def,
            cm_args_code_count_of_def, cm_args_arity_of_def,
            cm_binding_address_count_def, cm_binding_address_code_def,
            cm_push_code_def, cm_fp_relative_address_code_def,
            cm_load_code_def, cm_store_code_def, cm_temp_store_code_def,
            cm_temp_load_code_def, cm_char_normalize_code_def,
            cm_char_normalize_count_def, cm_binary_finish_code_def,
            cm_binary_tail_count_def, cm_return_epilogue_def,
            cm_emit_args_reload_def,
            cm_lcode_cond, cm_rcode_cond,
            cm_lcount_cond, cm_rcount_cond, cm_ilength_cond,
            get_theorem_by_name("ILENGTH_APPEND"),
            get_theorem_by_name("ILENGTH_DEF")));
      if (IS_NULL(reduced->solved)) {
        if (i == 8 && j == 1) {
          thm args_ih = assume_rule(
              `!(p:cm_program) fid pc slot scratch.
                 ilength
                   (cm_emit_args_store p fid pc slot scratch
                     (a1:(cm_expr)list)) +
                 ilength (cm_emit_args_reload p fid slot a1) + 1i ==
                 cm_args_code_count_of
                   (cm_args_code_counts p fid a1)`);
          ACCEPT_TAC(reduced, specl_rule(TERM_LIST(
              `p:cm_program`, `fid:int`, `pc:int`, `temp:int`,
              `(temp:int) + ilength (a1:(cm_expr)list)`), args_ih));
        } else if (i == 15) {
          thm tail_ih = assume_rule(
              `!(p:cm_program) fid pc slot scratch.
                 ilength
                   (cm_emit_args_store p fid pc slot scratch
                     (a1:(cm_expr)list)) +
                 ilength (cm_emit_args_reload p fid slot a1) + 1i ==
                 cm_args_code_count_of
                   (cm_args_code_counts p fid a1)`);
          thm tail_at = specl_rule(TERM_LIST(
              `p:cm_program`, `fid:int`,
              `(pc:int) +
                cm_rcount_of (cm_expr_code_counts p fid (a0:cm_expr)) +
                5i`,
              `(slot:int) + 1i`, `scratch:int`), tail_ih);
          ACCEPT_TAC(reduced, mp_rule(
              int_arith_rule(mk_imp(concl(tail_at),
                                    goal_ccl(reduced->g))),
              tail_at));
        } else {
          ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_expr_pair_and_args_code_lengths =
    cm_prove_expr_code_lengths();
PROOF thm cm_expr_pair_code_lengths =
    conjunct1_rule(cm_expr_pair_and_args_code_lengths);
PROOF thm cm_expr_code_lengths = conv_rule(
    pure_rewrite_conv(THM_LIST(
      gsym_rule(cm_emit_lvalue_def),
      gsym_rule(cm_emit_rvalue_def))),
    cm_expr_pair_code_lengths);
PROOF thm cm_args_code_lengths =
    conjunct2_rule(cm_expr_pair_and_args_code_lengths);

PROOF static thm cm_prove_stmt_code_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(stmt:cm_stmt). !(p:cm_program) fid pc temp breakpc continuepc.
         ilength
           (cm_emit_stmt p fid pc temp breakpc continuepc stmt) ==
         cm_stmt_code_count p fid stmt`);
  gnode_list cases = INDUCT_TAC(root, `stmt:cm_stmt`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode constructor_leaf = AUTO_INTROS_TAC(cases[i]);
    gnode_list frontier = AUTO_ASMP_DESTRUCT_TAC(constructor_leaf);
    gnode quantified = AUTO_INTROS_TAC(frontier[0]);
    gnode opened = CONV_TAC(quantified,
        once_rewrite_conv(THM_LIST(cm_emit_stmt_def)));
    gnode reduced = CONV_WITH_ASMP_TAC(
        opened, reduce_rewrite_conv, THM_LIST(
          cm_stmt_code_count_def, cm_expr_code_lengths,
          cm_char_normalize_code_def, cm_char_normalize_count_def,
          cm_fp_relative_address_code_def, cm_store_code_def,
          cm_return_epilogue_def, cm_ilength_cond,
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF")));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_stmt_code_length = cm_prove_stmt_code_length();

PROOF static thm cm_prove_param_stores_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(params:(cm_slot_d)list). !(p:cm_program) fid slot.
         ilength (cm_emit_param_stores p fid slot params) ==
         cm_param_stores_count params`);
  gnode_list cases = INDUCT_TAC(root, `params:(cm_slot_d)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    gnode opened = CONV_TAC(leaf,
        once_rewrite_conv(THM_LIST(
          cm_emit_param_stores_def, cm_param_stores_count_def)));
    gnode reduced = CONV_WITH_ASMP_TAC(
        opened, reduce_rewrite_conv, THM_LIST(
          cm_char_normalize_code_def, cm_char_normalize_count_def,
          cm_fp_relative_address_code_def, cm_store_code_def,
          cm_ilength_cond, get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF")));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_param_stores_length =
    cm_prove_param_stores_length();

PROOF static thm cm_prove_prologue_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid.
         ilength (cm_emit_prologue p fid) ==
         cm_function_prologue_count
           (inth fid (cm_program_functions p))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
      cm_emit_prologue_def, cm_function_prologue_count_def,
      cm_param_stores_length,
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("ILENGTH_DEF")));
  return gnode_prove(root);
}
PROOF thm cm_prologue_length = cm_prove_prologue_length();
PROOF thm get_cm_prologue_length(void) {
  return cm_prologue_length;
}

PROOF static thm cm_prove_function_code_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid.
         ilength (cm_emit_function p fid) ==
         cm_function_code_count p fid`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
      cm_emit_function_def, cm_function_code_count_def,
      cm_prologue_length, cm_stmt_code_length,
      cm_return_epilogue_def,
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("ILENGTH_DEF")));
  return gnode_prove(root);
}
PROOF thm cm_function_code_length =
    cm_prove_function_code_length();
PROOF thm get_cm_function_code_length(void) {
  return cm_function_code_length;
}

PROOF static thm cm_prove_functions_code_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list). !(p:cm_program) fid.
         ilength (cm_emit_functions p fid functions) ==
         cm_functions_code_size p functions fid`);
  gnode_list cases =
      INDUCT_TAC(root, `functions:(cm_function_d)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    gnode opened = CONV_TAC(leaf,
        once_rewrite_conv(THM_LIST(cm_emit_functions_def)));
    gnode reduced = CONV_WITH_ASMP_TAC(
        opened, reduce_rewrite_conv, THM_LIST(
          cm_functions_code_size_def, cm_function_code_length,
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF")));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_functions_code_length =
    cm_prove_functions_code_length();

PROOF static thm cm_prove_model_code_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         ilength (cm_model_code p) == cm_model_code_length p`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
      cm_model_code_def, cm_emit_prelude_def,
      cm_model_code_length_def, cm_functions_code_length,
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("ILENGTH_DEF")));
  return gnode_prove(root);
}
PROOF thm cm_model_code_length_exact =
    cm_prove_model_code_length();


PROOF static thm cm_prove_global_bytes_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list). !(g:cm_global_d).
         ilength (cm_global_bytes structs g) ==
         cm_global_model_size structs g`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list size_cases = BOOL_CASES_TAC(
      leaf, `0i <= cm_global_size
               (structs:(cm_struct_d)list) (g:cm_global_d)`,
      "hsize");
  thm nonnegative = assume_rule(
      `0i <= cm_global_size
         (structs:(cm_struct_d)list) (g:cm_global_d)`);
  thm replicated = mp_rule(ispecl_rule(TERM_LIST(
      `cm_global_size (structs:(cm_struct_d)list) (g:cm_global_d)`,
      `0i`), get_theorem_by_name("ILENGTH_IREPLICATE")),
      nonnegative);
  gnode_list init_cases = BOOL_CASES_TAC(size_cases[0],
      `cm_global_has_init (g:cm_global_d) &&
       ilength (cm_global_init_bytes g) <=
         cm_global_size (structs:(cm_struct_d)list) g`,
      "hinit");
  thm initialized = assume_rule(
      `cm_global_has_init (g:cm_global_d) &&
       ilength (cm_global_init_bytes g) <=
         cm_global_size (structs:(cm_struct_d)list) g`);
  thm init_fits = conjunct2_rule(initialized);
  thm pad_nonnegative = int_arith_rule(mk_imp(
      concl(init_fits),
      `0i <= cm_global_size
         (structs:(cm_struct_d)list) (g:cm_global_d) -
         ilength (cm_global_init_bytes g)`));
  pad_nonnegative = mp_rule(pad_nonnegative, init_fits);
  thm pad_length = mp_rule(ispecl_rule(TERM_LIST(
      `cm_global_size (structs:(cm_struct_d)list) (g:cm_global_d) -
         ilength (cm_global_init_bytes g)`,
      `0i`), get_theorem_by_name("ILENGTH_IREPLICATE")),
      pad_nonnegative);
  gnode init_done = CONV_WITH_ASMP_TAC(
      init_cases[0], reduce_rewrite_conv, THM_LIST(
        cm_global_bytes_def, cm_global_model_size_def,
        nonnegative, initialized, pad_length,
        get_theorem_by_name("ILENGTH_APPEND")));
  if (IS_NULL(init_done->solved)) {
    ACCEPT_TAC(init_done, int_arith_rule(goal_ccl(init_done->g)));
  }
  gnode zero_done = CONV_WITH_ASMP_TAC(
      init_cases[1], reduce_rewrite_conv, THM_LIST(
        cm_global_bytes_def, cm_global_model_size_def,
        nonnegative, replicated));
  if (IS_NULL(zero_done->solved)) {
    ACCEPT_TAC(zero_done, int_arith_rule(goal_ccl(zero_done->g)));
  }
  gnode negative_done = CONV_WITH_ASMP_TAC(
      size_cases[1], reduce_rewrite_conv, THM_LIST(
        cm_global_bytes_def, cm_global_model_size_def,
        get_theorem_by_name("ILENGTH_DEF")));
  if (IS_NULL(negative_done->solved)) {
    ACCEPT_TAC(negative_done,
      int_arith_rule(goal_ccl(negative_done->g)));
  }
  return gnode_prove(root);
}
PROOF thm cm_global_bytes_length =
    cm_prove_global_bytes_length();

PROOF static thm cm_prove_globals_bytes_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(globals:(cm_global_d)list).
         !(structs:(cm_struct_d)list).
         ilength (cm_globals_bytes structs globals) ==
         cm_globals_model_size structs globals`);
  gnode_list cases =
      INDUCT_TAC(root, `globals:(cm_global_d)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    gnode opened = CONV_TAC(leaf,
        once_rewrite_conv(THM_LIST(cm_globals_bytes_def)));
    gnode reduced = CONV_WITH_ASMP_TAC(
        opened, reduce_rewrite_conv, THM_LIST(
          cm_global_bytes_length, cm_globals_model_size_def,
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF")));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_globals_bytes_length =
    cm_prove_globals_bytes_length();

PROOF static thm cm_prove_strings_bytes_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(strings:(cm_string_d)list).
         ilength (cm_strings_bytes strings) ==
         cm_strings_size strings`);
  gnode_list cases =
      INDUCT_TAC(root, `strings:(cm_string_d)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    gnode opened = CONV_TAC(leaf,
        once_rewrite_conv(THM_LIST(cm_strings_bytes_def)));
    gnode reduced = CONV_WITH_ASMP_TAC(
        opened, reduce_rewrite_conv, THM_LIST(
          get_cm_strings_size_def(), get_cm_string_bytes_def(),
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF")));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_strings_bytes_length =
    cm_prove_strings_bytes_length();

PROOF static thm cm_prove_model_data_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         ilength (cm_model_data_bytes p) ==
         cm_model_data_size_count p`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm eight_zeros = mp_rule(ispecl_rule(TERM_LIST(`8i`, `0i`),
      get_theorem_by_name("ILENGTH_IREPLICATE")),
      int_arith_rule(`0i <= 8i`));
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      eight_zeros, cm_model_data_bytes_def,
      cm_model_data_size_count_def,
      cm_globals_bytes_length, cm_strings_bytes_length,
      get_theorem_by_name("ILENGTH_IREPLICATE"),
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("ILENGTH_DEF"))));
  return gnode_prove(root);
}
PROOF thm cm_model_data_bytes_length_exact =
    cm_prove_model_data_length();

PROOF thm cm_model_data_length_exact = conv_rule(
    pure_rewrite_conv(THM_LIST(
      gsym_rule(cm_model_data_length_def))),
    cm_model_data_bytes_length_exact);

PROOF static thm cm_prove_two_pass_layout(void) {
  thm code_length =
      spec_rule(`p:cm_program`, cm_model_code_length_exact);
  thm data_length =
      spec_rule(`p:cm_program`, cm_model_data_length_exact);
  thm object_shape = cm_compile_model_def;
  return gen_rule(`p:cm_program`,
      conj_rule(code_length, conj_rule(data_length, object_shape)));
}
PROOF thm cm_codegen_two_pass_layout =
    cm_prove_two_pass_layout();

PROOF static thm cm_prove_object_wf(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_wf_program p ==>
         tvm_object_wf (cm_compile_model p)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm admissible = assume_rule(
      `cm_wf_program (p:cm_program)`);
  thm admissible_parts = eq_mp_rule(
      apply_conversion(rewrite_conv(THM_LIST(
        cm_wf_program_def, cm_codegen_admissible_def)), concl(admissible)),
      admissible);
  thm fields = admissible_parts;
  for (size_t i = 0; i < 7; ++i) {
    fields = conjunct2_rule(fields);
  }
  fields = conjunct1_rule(fields);
  thm field_parts = eq_mp_rule(
      apply_conversion(rewrite_conv(THM_LIST(
        cm_codegen_fields_representable_def)), concl(fields)),
      fields);
  thm code_shape = conjunct1_rule(field_parts);
  thm targets = conjunct1_rule(conjunct2_rule(field_parts));
  thm patches =
      conjunct1_rule(conjunct2_rule(conjunct2_rule(field_parts)));
  thm entry =
      conjunct2_rule(conjunct2_rule(conjunct2_rule(field_parts)));
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      code_shape, targets, patches, entry, cm_compile_model_def,
      get_tvm_object_wf_def(), get_tvm_load_ok_def(),
      get_tvm_object_entry_def(), get_tvm_object_code_def(),
      get_tvm_object_patches_def())));
  return gnode_prove(root);
}
PROOF thm cmc_object_wf = cm_prove_object_wf();
PROOF thm get_cmc_object_wf(void) { return cmc_object_wf; }

PROOF thm get_cm_lvalue_code_count_def(void) {
  return cm_lvalue_code_count_def;
}
PROOF thm get_cm_rvalue_code_count_def(void) {
  return cm_rvalue_code_count_def;
}
PROOF thm get_cm_expr_code_counts_def(void) {
  return cm_expr_code_counts_def;
}
PROOF thm get_cm_lcount_of_def(void) { return cm_lcount_of_def; }
PROOF thm get_cm_rcount_of_def(void) { return cm_rcount_of_def; }
PROOF thm get_cm_args_code_counts_def(void) {
  return cm_expr_code_counts_def;
}
PROOF thm get_cm_args_code_count_of_def(void) {
  return cm_args_code_count_of_def;
}
PROOF thm get_cm_args_arity_of_def(void) {
  return cm_args_arity_of_def;
}
PROOF thm get_cm_i32_code_count_def(void) {
  return cm_i32_code_count_def;
}
PROOF thm get_cm_code_counts_representable_def(void) {
  return cm_code_counts_representable_def;
}
PROOF thm get_cm_expr_count_node_representable_def(void) {
  return cm_expr_count_node_representable_def;
}
PROOF thm get_cm_expr_counts_representable_def(void) {
  return cm_expr_counts_representable_def;
}
PROOF thm get_cm_args_counts_representable_def(void) {
  return cm_expr_counts_representable_def;
}
PROOF thm get_cm_char_normalize_count_def(void) {
  return cm_char_normalize_count_def;
}
PROOF thm get_cm_binding_address_count_def(void) {
  return cm_binding_address_count_def;
}
PROOF thm get_cm_binary_tail_count_def(void) {
  return cm_binary_tail_count_def;
}
PROOF thm get_cm_stmt_code_count_def(void) {
  return cm_stmt_code_count_def;
}
PROOF thm get_cm_function_code_count_def(void) {
  return cm_function_code_count_def;
}
PROOF thm get_cm_param_stores_count_def(void) {
  return cm_param_stores_count_def;
}
PROOF thm get_cm_function_prologue_count_def(void) {
  return cm_function_prologue_count_def;
}
PROOF thm get_cm_functions_code_size_def(void) {
  return cm_functions_code_size_def;
}
PROOF thm get_cm_function_prefix_def(void) {
  return cm_function_prefix_def;
}
PROOF thm get_cm_function_pc_def(void) { return cm_function_pc_def; }
PROOF thm get_cm_stmt_counts_representable_def(void) {
  return cm_stmt_counts_representable_def;
}
PROOF thm get_cm_param_counts_representable_def(void) {
  return cm_param_counts_representable_def;
}
PROOF thm get_cm_function_counts_representable_def(void) {
  return cm_function_counts_representable_def;
}
PROOF thm get_cm_functions_counts_representable_def(void) {
  return cm_functions_counts_representable_def;
}
PROOF thm get_cm_function_pcs_representable_def(void) {
  return cm_function_pcs_representable_def;
}
PROOF thm get_cm_model_code_length_def(void) {
  return cm_model_code_length_def;
}
PROOF thm get_cm_model_data_length_def(void) {
  return cm_model_data_length_def;
}
PROOF thm get_cm_global_model_size_def(void) {
  return cm_global_model_size_def;
}
PROOF thm get_cm_globals_model_size_def(void) {
  return cm_globals_model_size_def;
}
PROOF thm get_cm_model_data_size_count_def(void) {
  return cm_model_data_size_count_def;
}
PROOF thm get_cm_max_function_arity_from_def(void) {
  return cm_max_function_arity_from_def;
}
PROOF thm get_cm_max_function_arity_def(void) {
  return cm_max_function_arity_def;
}
PROOF thm get_cm_stack_bound_model_def(void) {
  return cm_stack_bound_model_def;
}
PROOF thm get_cm_char_normalize_code_def(void) {
  return cm_char_normalize_code_def;
}
PROOF thm get_cm_load_code_def(void) { return cm_load_code_def; }
PROOF thm get_cm_store_code_def(void) { return cm_store_code_def; }
PROOF thm get_cm_push_code_def(void) { return cm_push_code_def; }
PROOF thm get_cm_const_immediate_def(void) {
  return cm_const_immediate_def;
}
PROOF thm get_cm_param_offset_def(void) { return cm_param_offset_def; }
PROOF thm get_cm_local_offset_def(void) { return cm_local_offset_def; }
PROOF thm get_cm_temp_offset_def(void) { return cm_temp_offset_def; }
PROOF thm get_cm_fp_relative_address_code_def(void) {
  return cm_fp_relative_address_code_def;
}
PROOF thm get_cm_binding_address_code_def(void) {
  return cm_binding_address_code_def;
}
PROOF thm get_cm_temp_store_code_def(void) {
  return cm_temp_store_code_def;
}
PROOF thm get_cm_temp_load_code_def(void) {
  return cm_temp_load_code_def;
}
PROOF thm get_cm_binary_opcode_def(void) {
  return cm_binary_opcode_def;
}
PROOF thm get_cm_pointer_scale_def(void) {
  return cm_pointer_scale_def;
}
PROOF thm get_cm_binary_finish_code_def(void) {
  return cm_binary_finish_code_def;
}
PROOF thm get_cm_return_epilogue_def(void) {
  return cm_return_epilogue_def;
}
PROOF thm get_cm_emit_expr_pair_def(void) {
  return cm_emit_expr_pair_def;
}
PROOF thm get_cm_lcode_of_def(void) {
  return cm_lcode_of_def;
}
PROOF thm get_cm_rcode_of_def(void) {
  return cm_rcode_of_def;
}
PROOF thm get_cm_emit_args_reload_def(void) {
  return cm_emit_args_reload_def;
}
PROOF thm get_cm_emit_lvalue_def(void) {
  return cm_emit_lvalue_def;
}
PROOF thm get_cm_emit_rvalue_def(void) {
  return cm_emit_rvalue_def;
}
PROOF thm_list get_cm_codegen_eval_defs(void) {
  return THM_LIST(
      cm_lcount_of_def, cm_rcount_of_def,
      cm_args_code_count_of_def, cm_args_arity_of_def,
      cm_char_normalize_count_def, cm_binding_address_count_def,
      cm_binary_tail_count_def, cm_expr_code_counts_def,
      cm_lvalue_code_count_def, cm_rvalue_code_count_def,
      cm_stmt_code_count_def, cm_param_stores_count_def,
      cm_function_prologue_count_def, cm_function_code_count_def,
      cm_functions_code_size_def, cm_function_prefix_def,
      cm_function_pc_def, cm_model_code_length_def,
      cm_lcode_of_def, cm_rcode_of_def, cm_push_code_def,
      cm_const_immediate_def, cm_char_normalize_code_def,
      cm_load_code_def,
      cm_store_code_def, cm_param_offset_def, cm_local_offset_def,
      cm_temp_offset_def, cm_fp_relative_address_code_def,
      cm_binding_address_code_def, cm_temp_store_code_def,
      cm_temp_load_code_def, cm_binary_opcode_def,
      cm_pointer_scale_def, cm_binary_finish_code_def,
      cm_return_epilogue_def, cm_emit_args_reload_def,
      cm_emit_expr_pair_def, cm_emit_lvalue_def,
      cm_emit_rvalue_def, cm_emit_stmt_def,
      cm_emit_param_stores_def, cm_emit_prologue_def,
      cm_emit_function_def, cm_emit_functions_def,
      cm_emit_prelude_def, cm_model_code_def,
      cm_global_init_bytes_def, cm_global_bytes_def,
      cm_global_model_size_def, cm_globals_model_size_def,
      cm_model_data_size_count_def, cm_globals_bytes_def,
      cm_strings_bytes_def, cm_model_data_bytes_def,
      cm_bytes_patches_def, cm_model_patches_def,
      cm_compile_model_def, cm_model_data_length_def);
}

PROOF thm get_cm_emit_stmt_def(void) { return cm_emit_stmt_def; }
PROOF thm get_cm_emit_param_stores_def(void) {
  return cm_emit_param_stores_def;
}
PROOF thm get_cm_emit_prologue_def(void) {
  return cm_emit_prologue_def;
}
PROOF thm get_cm_emit_function_def(void) {
  return cm_emit_function_def;
}
PROOF thm get_cm_emit_functions_def(void) {
  return cm_emit_functions_def;
}
PROOF thm get_cm_emit_prelude_def(void) {
  return cm_emit_prelude_def;
}
PROOF thm get_cm_model_code_def(void) { return cm_model_code_def; }
PROOF thm get_cm_model_data_bytes_def(void) {
  return cm_model_data_bytes_def;
}
PROOF thm get_cm_global_init_bytes_def(void) {
  return cm_global_init_bytes_def;
}
PROOF thm get_cm_global_bytes_def(void) {
  return cm_global_bytes_def;
}
PROOF thm get_cm_globals_bytes_def(void) {
  return cm_globals_bytes_def;
}
PROOF thm get_cm_strings_bytes_def(void) {
  return cm_strings_bytes_def;
}
PROOF thm get_cm_bytes_patches_def(void) {
  return cm_bytes_patches_def;
}
PROOF thm get_cm_model_patches_def(void) {
  return cm_model_patches_def;
}
PROOF thm get_cm_compile_model_def(void) {
  return cm_compile_model_def;
}
PROOF thm get_cm_stack_height_max_def(void) {
  return cm_stack_height_max_def;
}
PROOF thm get_cm_stack_at_def(void) { return cm_stack_at_def; }
PROOF thm get_cm_stack_head_ok_def(void) {
  return cm_stack_head_ok_def;
}
PROOF thm get_cm_stack_edges_from_def(void) {
  return cm_stack_edges_from_def;
}
PROOF thm get_cm_stack_call_insts_from_def(void) {
  return cm_stack_call_insts_from_def;
}
PROOF thm get_cm_stack_call_sites_def(void) {
  return cm_stack_call_sites_def;
}
PROOF thm get_cm_stack_certificate_def(void) {
  return cm_stack_certificate_def;
}
PROOF thm get_cm_stack_summary_def(void) {
  return cm_stack_summary_def;
}
PROOF thm get_cm_codegen_fields_representable_def(void) {
  return cm_codegen_fields_representable_def;
}
PROOF thm get_cm_codegen_counts_representable_def(void) {
  return cm_codegen_counts_representable_def;
}
PROOF thm get_cm_codegen_admissible_def(void) {
  return cm_codegen_admissible_def;
}
PROOF thm get_cm_wf_program_def(void) {
  return cm_wf_program_def;
}
PROOF thm get_cm_expr_code_lengths(void) {
  return cm_expr_code_lengths;
}
PROOF thm get_cm_args_code_lengths(void) {
  return cm_args_code_lengths;
}
PROOF thm get_cm_stmt_code_length(void) {
  return cm_stmt_code_length;
}
PROOF thm get_cm_model_code_length_exact(void) {
  return cm_model_code_length_exact;
}
PROOF thm get_cm_model_data_length_exact(void) {
  return cm_model_data_length_exact;
}
PROOF thm get_cm_codegen_two_pass_layout(void) {
  return cm_codegen_two_pass_layout;
}

PROOF static int _cmc_codegen_audit(void) {
  ENSURE_COND(alpha_compare(concl(cm_stack_bound_model_def),
      `cm_stack_bound_model (p:cm_program) ==
       3i + cm_max_function_arity p`) == 0,
      "compiler stack bound is not 3 + maximum arity");
  ENSURE_COND(alpha_compare(concl(cm_compile_model_def),
      `cm_compile_model (p:cm_program) ==
       TVMObject 0i (cm_model_code p) (cm_model_patches p)`) == 0,
      "compiler object is not the direct resolved TVM image");
  ENSURE_COND(alpha_compare(concl(cm_emit_prelude_def),
      `cm_emit_prelude (p:cm_program) ==
       [TVMInst TVMPushOp 1048576i;
        TVMInst TVMPushOp 8i; TVMInst TVMStoreOp 0i;
        TVMInst TVMCallOp (cm_function_pc p (cm_program_main p));
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMAddOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMHaltOp 0i]`) == 0,
      "compiler prelude or six-instruction status normalization changed");
  ENSURE_COND(alpha_compare(concl(cm_codegen_two_pass_layout),
      `!(p:cm_program).
         ilength (cm_model_code p) == cm_model_code_length p &&
         cm_model_data_length p == cm_model_data_size_count p &&
         cm_compile_model p ==
           TVMObject 0i (cm_model_code p) (cm_model_patches p)`) == 0,
      "compiler two-pass layout theorem has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(cmc_object_wf),
      `!(p:cm_program).
         cm_wf_program p ==>
         tvm_object_wf (cm_compile_model p)`) == 0,
      "compiler object well-formedness theorem has the wrong conclusion");
  ENSURE_COND(vector_size(hyp(cm_model_code_length_exact)) == 0 &&
              vector_size(hyp(cm_model_data_length_exact)) == 0 &&
              vector_size(hyp(cmc_object_wf)) == 0,
              "compiler layout or object theorem is not closed");
  ENSURE_COND(vector_size(get_all_axioms()) ==
                _cmc_codegen_axioms_before,
              "cmc_codegen introduced an axiom");
  return 0;
err:
  ERR_FUN_PUTS("_cmc_codegen_audit");
  return -1;
}
PROOF int _cmc_codegen_audit_run = _cmc_codegen_audit();
