#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_ready_context.h"

#require "cmc_annotate_model.c"

PROOF static size_t _cmc_preservation_ready_context_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_phase_accepts_statement_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(cm_phase_accepts_statement CAHaltP = F) &&
     (!ty. cm_phase_accepts_statement (CALoadP (ty:cm_type)) = F) &&
     (!src ty. cm_phase_accepts_statement
        (CAAssignLP (src:cm_expr) (ty:cm_type)) = F) &&
     (!ptr ty. cm_phase_accepts_statement
        (CAAssignRP (ptr:cm_value) (ty:cm_type)) = F) &&
     (!op left right ty. cm_phase_accepts_statement
        (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
          (ty:cm_type)) = F) &&
     (!op left right value ty. cm_phase_accepts_statement
        (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
          (value:cm_value) (ty:cm_type)) = F) &&
     (!op. cm_phase_accepts_statement (CAUnaryP (op:int)) = F) &&
     (!index ty. cm_phase_accepts_statement
        (CAIndexLP (index:cm_expr) (ty:cm_type)) = F) &&
     (!base ty. cm_phase_accepts_statement
        (CAIndexRP (base:cm_value) (ty:cm_type)) = F) &&
     (!mid base_ty. cm_phase_accepts_statement
        (CAMemberP (mid:int) (base_ty:cm_type)) = F) &&
     (cm_phase_accepts_statement CAPutcP = F) &&
     (cm_phase_accepts_statement CAPutiP = F) &&
     (cm_phase_accepts_statement CAExitP = F) &&
     (cm_phase_accepts_statement CAExprStmtP = F) &&
     (!slot. cm_phase_accepts_statement (CAInitP (slot:int)) = F) &&
     (!env regions jump target. cm_phase_accepts_statement
        (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
          (jump:bool) (target:int)) = T) &&
     (!second. cm_phase_accepts_statement
        (CASeqP (second:cm_stmt)) = T) &&
     (!yes no. cm_phase_accepts_statement
        (CAIfP (yes:cm_stmt) (no:cm_stmt)) = F) &&
     (!guard body loop_start loop_end. cm_phase_accepts_statement
        (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
          (loop_start:int) (loop_end:int)) = F) &&
     (!guard body env regions loop_start loop_end.
        cm_phase_accepts_statement
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
            (env:int->int->cm_value) (regions:(cm_region)list)
            (loop_start:int) (loop_end:int)) = T) &&
     (cm_phase_accepts_statement CAReturnP = F) &&
     (!callee rest values ret all_args base_slot current_slot scratch.
        cm_phase_accepts_statement
          (CAArgP (callee:int) (rest:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int)) = F) &&
     (!caller env fp regions ret. cm_phase_accepts_statement
        (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
          (regions:(cm_region)list) (ret:cm_type)) = T)`);
PROOF static int _c_cm_phase_accepts_statement =
    cst_add_const_to_header(`cm_phase_accepts_statement`);

PROOF thm cm_phase_requires_statement_parent_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(cm_phase_requires_statement_parent CAHaltP = F) &&
     (!ty. cm_phase_requires_statement_parent
        (CALoadP (ty:cm_type)) = F) &&
     (!src ty. cm_phase_requires_statement_parent
        (CAAssignLP (src:cm_expr) (ty:cm_type)) = F) &&
     (!ptr ty. cm_phase_requires_statement_parent
        (CAAssignRP (ptr:cm_value) (ty:cm_type)) = F) &&
     (!op left right ty. cm_phase_requires_statement_parent
        (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
          (ty:cm_type)) = F) &&
     (!op left right value ty. cm_phase_requires_statement_parent
        (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
          (value:cm_value) (ty:cm_type)) = F) &&
     (!op. cm_phase_requires_statement_parent
        (CAUnaryP (op:int)) = F) &&
     (!index ty. cm_phase_requires_statement_parent
        (CAIndexLP (index:cm_expr) (ty:cm_type)) = F) &&
     (!base ty. cm_phase_requires_statement_parent
        (CAIndexRP (base:cm_value) (ty:cm_type)) = F) &&
     (!mid base_ty. cm_phase_requires_statement_parent
        (CAMemberP (mid:int) (base_ty:cm_type)) = F) &&
     (cm_phase_requires_statement_parent CAPutcP = F) &&
     (cm_phase_requires_statement_parent CAPutiP = F) &&
     (cm_phase_requires_statement_parent CAExitP = F) &&
     (cm_phase_requires_statement_parent CAExprStmtP = T) &&
     (!slot. cm_phase_requires_statement_parent
        (CAInitP (slot:int)) = T) &&
     (!env regions jump target. cm_phase_requires_statement_parent
        (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
          (jump:bool) (target:int)) = T) &&
     (!second. cm_phase_requires_statement_parent
        (CASeqP (second:cm_stmt)) = T) &&
     (!yes no. cm_phase_requires_statement_parent
        (CAIfP (yes:cm_stmt) (no:cm_stmt)) = T) &&
     (!guard body loop_start loop_end.
        cm_phase_requires_statement_parent
          (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
            (loop_start:int) (loop_end:int)) = T) &&
     (!guard body env regions loop_start loop_end.
        cm_phase_requires_statement_parent
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
            (env:int->int->cm_value) (regions:(cm_region)list)
            (loop_start:int) (loop_end:int)) = T) &&
     (cm_phase_requires_statement_parent CAReturnP = T) &&
     (!callee rest values ret all_args base_slot current_slot scratch.
        cm_phase_requires_statement_parent
          (CAArgP (callee:int) (rest:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int)) = F) &&
     (!caller env fp regions ret. cm_phase_requires_statement_parent
        (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
          (regions:(cm_region)list) (ret:cm_type)) = F)`);
PROOF static int _c_cm_phase_requires_statement_parent =
    cst_add_const_to_header(`cm_phase_requires_statement_parent`);

PROOF thm cm_phase_control_scope_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(cm_phase_control_scope CAHaltP = 3i) &&
     (!ty. cm_phase_control_scope (CALoadP (ty:cm_type)) = 0i) &&
     (!src ty. cm_phase_control_scope
        (CAAssignLP (src:cm_expr) (ty:cm_type)) = 0i) &&
     (!ptr ty. cm_phase_control_scope
        (CAAssignRP (ptr:cm_value) (ty:cm_type)) = 0i) &&
     (!op left right ty. cm_phase_control_scope
        (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
          (ty:cm_type)) = 0i) &&
     (!op left right value ty. cm_phase_control_scope
        (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
          (value:cm_value) (ty:cm_type)) = 0i) &&
     (!op. cm_phase_control_scope (CAUnaryP (op:int)) = 0i) &&
     (!index ty. cm_phase_control_scope
        (CAIndexLP (index:cm_expr) (ty:cm_type)) = 0i) &&
     (!base ty. cm_phase_control_scope
        (CAIndexRP (base:cm_value) (ty:cm_type)) = 0i) &&
     (!mid base_ty. cm_phase_control_scope
        (CAMemberP (mid:int) (base_ty:cm_type)) = 0i) &&
     (cm_phase_control_scope CAPutcP = 0i) &&
     (cm_phase_control_scope CAPutiP = 0i) &&
     (cm_phase_control_scope CAExitP = 0i) &&
     (cm_phase_control_scope CAExprStmtP = 0i) &&
     (!slot. cm_phase_control_scope (CAInitP (slot:int)) = 0i) &&
     (!env regions jump target. cm_phase_control_scope
        (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
          (jump:bool) (target:int)) = 0i) &&
     (!second. cm_phase_control_scope
        (CASeqP (second:cm_stmt)) = 0i) &&
     (!yes no. cm_phase_control_scope
        (CAIfP (yes:cm_stmt) (no:cm_stmt)) = 0i) &&
     (!guard body loop_start loop_end. cm_phase_control_scope
        (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
          (loop_start:int) (loop_end:int)) = 0i) &&
     (!guard body env regions loop_start loop_end.
        cm_phase_control_scope
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
            (env:int->int->cm_value) (regions:(cm_region)list)
            (loop_start:int) (loop_end:int)) = 1i) &&
     (cm_phase_control_scope CAReturnP = 0i) &&
     (!callee rest values ret all_args base_slot current_slot scratch.
        cm_phase_control_scope
          (CAArgP (callee:int) (rest:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int)) = 0i) &&
     (!caller env fp regions ret. cm_phase_control_scope
        (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
          (regions:(cm_region)list) (ret:cm_type)) = 2i)`);
PROOF static int _c_cm_phase_control_scope =
    cst_add_const_to_header(`cm_phase_control_scope`);

PROOF thm cm_cursors_loop_ready_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_cursors_loop_ready ([]:(cm_acursor)list) = F) &&
     (!cursor rest. cm_cursors_loop_ready
        ((cursor:cm_acursor) :: (rest:(cm_acursor)list)) =
        (if cm_phase_control_scope (cm_cursor_phase cursor) == 1i
         then T
         else if cm_phase_control_scope (cm_cursor_phase cursor) == 2i ||
                 cm_phase_control_scope (cm_cursor_phase cursor) == 3i
              then F
              else cm_cursors_loop_ready rest))`);
PROOF static int _c_cm_cursors_loop_ready =
    cst_add_const_to_header(`cm_cursors_loop_ready`);

PROOF thm cm_cursors_call_ready_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_cursors_call_ready ([]:(cm_acursor)list) = F) &&
     (!cursor rest. cm_cursors_call_ready
        ((cursor:cm_acursor) :: (rest:(cm_acursor)list)) =
        (if cm_phase_control_scope (cm_cursor_phase cursor) == 2i
         then T
         else if cm_phase_control_scope (cm_cursor_phase cursor) == 3i
              then F
              else cm_cursors_call_ready rest))`);
PROOF static int _c_cm_cursors_call_ready =
    cst_add_const_to_header(`cm_cursors_call_ready`);

PROOF thm cm_stmt_context_ready_def = new_rec_definition(
    get_cm_stmt_recursion(),
    `(!cursors. cm_stmt_context_ready CMSkipS
        (cursors:(cm_acursor)list) = T) &&
     (!expr cursors. cm_stmt_context_ready
        (CMExprS (expr:cm_expr)) (cursors:(cm_acursor)list) = T) &&
     (!slot cursors. cm_stmt_context_ready
        (CMDeclS (slot:int)) (cursors:(cm_acursor)list) = T) &&
     (!slot expr cursors. cm_stmt_context_ready
        (CMInitS (slot:int) (expr:cm_expr))
        (cursors:(cm_acursor)list) = T) &&
     (!first second cursors. cm_stmt_context_ready
        (CMSeqS (first:cm_stmt) (second:cm_stmt))
        (cursors:(cm_acursor)list) = T) &&
     (!body cursors. cm_stmt_context_ready
        (CMBlockS (body:cm_stmt)) (cursors:(cm_acursor)list) = T) &&
     (!guard yes no cursors. cm_stmt_context_ready
        (CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt))
        (cursors:(cm_acursor)list) = T) &&
     (!guard body cursors. cm_stmt_context_ready
        (CMWhileS (guard:cm_expr) (body:cm_stmt))
        (cursors:(cm_acursor)list) = T) &&
     (!cursors. cm_stmt_context_ready CMBreakS
        (cursors:(cm_acursor)list) =
        cm_cursors_loop_ready cursors) &&
     (!cursors. cm_stmt_context_ready CMContinueS
        (cursors:(cm_acursor)list) =
        cm_cursors_loop_ready cursors) &&
     (!expr cursors. cm_stmt_context_ready
        (CMReturnS (expr:cm_expr)) (cursors:(cm_acursor)list) =
        cm_cursors_call_ready cursors)`);
PROOF static int _c_cm_stmt_context_ready =
    cst_add_const_to_header(`cm_stmt_context_ready`);
PROOF thm cm_stmt_scope_ready_def = new_rec_definition(
    get_cm_stmt_recursion(),
    `(!loop_ok call_ok. cm_stmt_scope_ready
        (loop_ok:bool) (call_ok:bool) CMSkipS = T) &&
     (!loop_ok call_ok expr. cm_stmt_scope_ready loop_ok call_ok
        (CMExprS (expr:cm_expr)) = T) &&
     (!loop_ok call_ok slot. cm_stmt_scope_ready loop_ok call_ok
        (CMDeclS (slot:int)) = T) &&
     (!loop_ok call_ok slot expr. cm_stmt_scope_ready loop_ok call_ok
        (CMInitS (slot:int) (expr:cm_expr)) = T) &&
     (!loop_ok call_ok first second. cm_stmt_scope_ready loop_ok call_ok
        (CMSeqS (first:cm_stmt) (second:cm_stmt)) =
        (cm_stmt_scope_ready loop_ok call_ok first &&
         cm_stmt_scope_ready loop_ok call_ok second)) &&
     (!loop_ok call_ok body. cm_stmt_scope_ready loop_ok call_ok
        (CMBlockS (body:cm_stmt)) =
        cm_stmt_scope_ready loop_ok call_ok body) &&
     (!loop_ok call_ok guard yes no. cm_stmt_scope_ready loop_ok call_ok
        (CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)) =
        (cm_stmt_scope_ready loop_ok call_ok yes &&
         cm_stmt_scope_ready loop_ok call_ok no)) &&
     (!loop_ok call_ok guard body. cm_stmt_scope_ready loop_ok call_ok
        (CMWhileS (guard:cm_expr) (body:cm_stmt)) =
        cm_stmt_scope_ready T call_ok body) &&
     (!loop_ok call_ok. cm_stmt_scope_ready loop_ok call_ok CMBreakS =
        loop_ok) &&
     (!loop_ok call_ok. cm_stmt_scope_ready loop_ok call_ok
        CMContinueS = loop_ok) &&
     (!loop_ok call_ok expr. cm_stmt_scope_ready loop_ok call_ok
        (CMReturnS (expr:cm_expr)) = call_ok)`);
PROOF static int _c_cm_stmt_scope_ready =
    cst_add_const_to_header(`cm_stmt_scope_ready`);

PROOF thm cm_phase_scope_ready_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(!rest. cm_phase_scope_ready CAHaltP
        (rest:(cm_acursor)list) = T) &&
     (!ty rest. cm_phase_scope_ready (CALoadP (ty:cm_type)) rest = T) &&
     (!src ty rest. cm_phase_scope_ready
        (CAAssignLP (src:cm_expr) (ty:cm_type)) rest = T) &&
     (!ptr ty rest. cm_phase_scope_ready
        (CAAssignRP (ptr:cm_value) (ty:cm_type)) rest = T) &&
     (!op left right ty rest. cm_phase_scope_ready
        (CABinLP (op:int) (left:cm_expr) (right:cm_expr) (ty:cm_type))
        rest = T) &&
     (!op left right value ty rest. cm_phase_scope_ready
        (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
          (value:cm_value) (ty:cm_type)) rest = T) &&
     (!op rest. cm_phase_scope_ready (CAUnaryP (op:int)) rest = T) &&
     (!index ty rest. cm_phase_scope_ready
        (CAIndexLP (index:cm_expr) (ty:cm_type)) rest = T) &&
     (!base ty rest. cm_phase_scope_ready
        (CAIndexRP (base:cm_value) (ty:cm_type)) rest = T) &&
     (!mid base_ty rest. cm_phase_scope_ready
        (CAMemberP (mid:int) (base_ty:cm_type)) rest = T) &&
     (!rest. cm_phase_scope_ready CAPutcP rest = T) &&
     (!rest. cm_phase_scope_ready CAPutiP rest = T) &&
     (!rest. cm_phase_scope_ready CAExitP rest = T) &&
     (!rest. cm_phase_scope_ready CAExprStmtP rest = T) &&
     (!slot rest. cm_phase_scope_ready (CAInitP (slot:int)) rest = T) &&
     (!env regions jump target rest. cm_phase_scope_ready
        (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
          (jump:bool) (target:int)) rest = T) &&
     (!second rest. cm_phase_scope_ready
        (CASeqP (second:cm_stmt)) rest =
        cm_stmt_scope_ready
          (cm_cursors_loop_ready rest)
          (cm_cursors_call_ready rest) second) &&
     (!yes no rest. cm_phase_scope_ready
        (CAIfP (yes:cm_stmt) (no:cm_stmt)) rest =
        (cm_stmt_scope_ready
           (cm_cursors_loop_ready rest)
           (cm_cursors_call_ready rest) yes &&
         cm_stmt_scope_ready
           (cm_cursors_loop_ready rest)
           (cm_cursors_call_ready rest) no)) &&
     (!guard body loop_start loop_end rest. cm_phase_scope_ready
        (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
          (loop_start:int) (loop_end:int)) rest =
        cm_stmt_scope_ready T (cm_cursors_call_ready rest) body) &&
     (!guard body env regions loop_start loop_end rest.
        cm_phase_scope_ready
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
            (env:int->int->cm_value) (regions:(cm_region)list)
            (loop_start:int) (loop_end:int)) rest =
        cm_stmt_scope_ready T (cm_cursors_call_ready rest) body) &&
     (!rest. cm_phase_scope_ready CAReturnP rest = T) &&
     (!callee args values ret all_args base_slot current_slot scratch rest.
        cm_phase_scope_ready
          (CAArgP (callee:int) (args:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int)) rest = T) &&
     (!caller env fp regions ret rest. cm_phase_scope_ready
        (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
          (regions:(cm_region)list) (ret:cm_type)) rest = T)`);
PROOF static int _c_cm_phase_scope_ready =
    cst_add_const_to_header(`cm_phase_scope_ready`);

PROOF thm cm_cursors_scope_ready_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_cursors_scope_ready ([]:(cm_acursor)list) = T) &&
     (!cursor rest. cm_cursors_scope_ready
        ((cursor:cm_acursor) :: (rest:(cm_acursor)list)) =
        (cm_cursors_scope_ready rest &&
         cm_phase_scope_ready (cm_cursor_phase cursor) rest))`);
PROOF static int _c_cm_cursors_scope_ready =
    cst_add_const_to_header(`cm_cursors_scope_ready`);


PROOF thm cm_control_context_ready_def = new_fun_definition(
    `cm_control_context_ready (ctl:cm_control)
       (cursors:(cm_acursor)list) =
       (if cm_control_kind ctl == 1i ||
           cm_control_kind ctl == 2i
        then cm_cursors_loop_ready cursors
        else if cm_control_kind ctl == 3i
             then cm_cursors_call_ready cursors
             else T)`);
PROOF static int _c_cm_control_context_ready =
    cst_add_const_to_header(`cm_control_context_ready`);

PROOF thm cm_statement_cursors_ready_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_statement_cursors_ready ([]:(cm_acursor)list) = F) &&
     (!cursor rest. cm_statement_cursors_ready
        ((cursor:cm_acursor) :: (rest:(cm_acursor)list)) =
        cm_phase_accepts_statement (cm_cursor_phase cursor))`);
PROOF static int _c_cm_statement_cursors_ready =
    cst_add_const_to_header(`cm_statement_cursors_ready`);

PROOF thm cm_cursors_context_ready_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_cursors_context_ready ([]:(cm_acursor)list) = T) &&
     (!cursor rest. cm_cursors_context_ready
        ((cursor:cm_acursor) :: (rest:(cm_acursor)list)) =
        (cm_cursors_context_ready rest &&
         (cm_cursor_phase cursor == CAHaltP ==> rest == []) &&
         (cm_phase_requires_statement_parent (cm_cursor_phase cursor) ==>
          cm_statement_cursors_ready rest) &&
         (cm_cursor_phase cursor == CAReturnP ==>
          cm_cursors_call_ready rest)))`);
PROOF static int _c_cm_cursors_context_ready =
    cst_add_const_to_header(`cm_cursors_context_ready`);

PROOF thm cm_task_context_ready_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!q input ann. cm_task_context_ready
        (CMStartTask (q:cm_program) (input:(int)list))
        (ann:cm_annotation) =
        (cm_cursors_context_ready (cm_ann_cursors ann) &&
         cm_cursors_scope_ready (cm_ann_cursors ann))) &&
     (!q fid expr st ks ann. cm_task_context_ready
        (CMRTask (q:cm_program) (fid:int) (expr:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (cm_cursors_context_ready (cm_ann_cursors ann) &&
         cm_cursors_scope_ready (cm_ann_cursors ann))) &&
     (!q fid expr st ks ann. cm_task_context_ready
        (CMLTask (q:cm_program) (fid:int) (expr:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (cm_cursors_context_ready (cm_ann_cursors ann) &&
         cm_cursors_scope_ready (cm_ann_cursors ann))) &&
     (!q fid stmt st ks ann. cm_task_context_ready
        (CMSTask (q:cm_program) (fid:int) (stmt:cm_stmt)
          (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (cm_cursors_context_ready (cm_ann_cursors ann) &&
         cm_cursors_scope_ready (cm_ann_cursors ann) &&
         cm_statement_cursors_ready (cm_ann_cursors ann) &&
         cm_stmt_context_ready stmt (cm_ann_cursors ann) &&
         cm_stmt_scope_ready
           (cm_cursors_loop_ready (cm_ann_cursors ann))
           (cm_cursors_call_ready (cm_ann_cursors ann)) stmt)) &&
     (!q fid value st ks ann. cm_task_context_ready
        (CMVTask (q:cm_program) (fid:int) (value:cm_value)
          (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (cm_cursors_context_ready (cm_ann_cursors ann) &&
         cm_cursors_scope_ready (cm_ann_cursors ann))) &&
     (!q fid ctl st ks ann. cm_task_context_ready
        (CMCTask (q:cm_program) (fid:int) (ctl:cm_control)
          (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (cm_cursors_context_ready (cm_ann_cursors ann) &&
         cm_cursors_scope_ready (cm_ann_cursors ann) &&
         cm_control_context_ready ctl (cm_ann_cursors ann))) &&
     (!st ctl status ann. cm_task_context_ready
        (CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int))
        (ann:cm_annotation) =
        (cm_cursors_context_ready (cm_ann_cursors ann) &&
         cm_cursors_scope_ready (cm_ann_cursors ann)))`);
PROOF static int _c_cm_task_context_ready =
    cst_add_const_to_header(`cm_task_context_ready`);

PROOF static thm cm_prove_task_context_initial(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         cm_task_context_ready (CMStartTask p input)
           cm_initial_annotation`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_task_context_ready_def, cm_initial_annotation_def,
      cm_ann_cursors_def, cm_cursors_context_ready_def,
      cm_cursors_scope_ready_def)));
  return gnode_prove(root);
}
PROOF thm cm_task_context_initial =
    cm_prove_task_context_initial();


PROOF static int cmc_preservation_ready_context_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_ready_context_axioms_before,
      "cmc_preservation_ready_context introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_ready_context_checks =
    cmc_preservation_ready_context_final_checks();
