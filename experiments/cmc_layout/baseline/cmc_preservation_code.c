#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_tvm.h"
#require "cmc_preservation_tvm.c"
#include "cmc_preservation_state.h"
#require "cmc_preservation_state.c"
#include "cmc_preservation_code.h"

PROOF static size_t _cmc_preservation_code_axioms_before =
    vector_size(get_all_axioms());

/* Code physically following a value at the head continuation cursor. */
PROOF thm cm_value_phase_code_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(!p fid pc temp owner breakpc continuepc.
        cm_value_phase_code (p:cm_program) (fid:int) (pc:int)
          (temp:int) (owner:int) (breakpc:int) (continuepc:int)
          CAHaltP = cm_status_tail_code) &&
     (!p fid pc temp owner breakpc continuepc ty.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          (CALoadP (ty:cm_type)) = cm_load_code ty) &&
     (!p fid pc temp owner breakpc continuepc src ty.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          (CAAssignLP (src:cm_expr) (ty:cm_type)) =
        cm_temp_store_code p fid owner ++
        cm_emit_rvalue p fid
          (pc + ilength (cm_temp_store_code p fid owner))
          (owner + 1i) src ++
        cm_assign_tail_code p fid ty owner) &&
     (!p fid pc temp owner breakpc continuepc ptr ty.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          (CAAssignRP (ptr:cm_value) (ty:cm_type)) =
        cm_assign_tail_code p fid ty owner) &&
     (!p fid pc temp owner breakpc continuepc op left right ty.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
             (ty:cm_type)) =
        (if op == 0i || op == 1i
         then [TVMInst (if op == 0i then TVMJnzOp else TVMJzOp)
                 (pc + cm_rvalue_code_count p fid right + 4i)] ++
              cm_emit_rvalue p fid (pc + 1i) owner right ++
              [TVMInst TVMPushOp 0i; TVMInst TVMNeOp 0i;
               TVMInst TVMJmpOp
                 (pc + cm_rvalue_code_count p fid right + 5i);
               TVMInst TVMPushOp (if op == 0i then 1i else 0i)]
         else cm_temp_store_code p fid owner ++
              cm_emit_rvalue p fid
                (pc + ilength (cm_temp_store_code p fid owner))
                (owner + 1i) right ++
              cm_binary_finish_code p fid op left right owner)) &&
     (!p fid pc temp owner breakpc continuepc op left right value ty.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
             (value:cm_value) (ty:cm_type)) =
        (if op == 0i || op == 1i
         then [TVMInst TVMPushOp 0i; TVMInst TVMNeOp 0i;
               TVMInst TVMJmpOp (pc + 4i);
               TVMInst TVMPushOp (if op == 0i then 1i else 0i)]
         else cm_binary_finish_code p fid op left right owner)) &&
     (!p fid pc temp owner breakpc continuepc op.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          (CAUnaryP (op:int)) =
        [TVMInst TVMPushOp (if op == 0i then --1i else 0i);
         TVMInst (if op == 0i then TVMMulOp else TVMEqOp) 0i]) &&
     (!p fid pc temp owner breakpc continuepc index ty.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          (CAIndexLP (index:cm_expr) (ty:cm_type)) =
        cm_temp_store_code p fid owner ++
        cm_emit_rvalue p fid
          (pc + ilength (cm_temp_store_code p fid owner))
          (owner + 1i) index ++
        cm_index_tail_code p fid ty owner) &&
     (!p fid pc temp owner breakpc continuepc base ty.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          (CAIndexRP (base:cm_value) (ty:cm_type)) =
        cm_index_tail_code p fid ty owner) &&
     (!p fid pc temp owner breakpc continuepc mid base_ty.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          (CAMemberP (mid:int) (base_ty:cm_type)) =
        cm_member_tail_code p base_ty mid) &&
     (!p fid pc temp owner breakpc continuepc.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          CAPutcP = [TVMInst TVMDupOp 0i; TVMInst TVMPutcOp 0i]) &&
     (!p fid pc temp owner breakpc continuepc.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          CAPutiP = [TVMInst TVMDupOp 0i; TVMInst TVMPutiOp 0i]) &&
     (!p fid pc temp owner breakpc continuepc.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          CAExitP = cm_status_tail_code) &&
     (!p fid pc temp owner breakpc continuepc.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          CAExprStmtP = [TVMInst TVMPopOp 0i]) &&
     (!p fid pc temp owner breakpc continuepc slot.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          (CAInitP (slot:int)) = cm_init_tail_code p fid slot) &&
     (!p fid pc temp owner breakpc continuepc env regions jump target.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
             (jump:bool) (target:int)) =
        (if jump then [TVMInst TVMJmpOp target] else [])) &&
     (!p fid pc temp owner breakpc continuepc second.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          (CASeqP (second:cm_stmt)) =
        cm_emit_stmt p fid pc owner breakpc continuepc second) &&
     (!p fid pc temp owner breakpc continuepc yes no.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          (CAIfP (yes:cm_stmt) (no:cm_stmt)) =
        [TVMInst TVMJzOp
           (pc + 1i + cm_stmt_code_count p fid yes + 1i)] ++
        cm_emit_stmt p fid (pc + 1i) owner breakpc continuepc yes ++
        [TVMInst TVMJmpOp
           (pc + 2i + cm_stmt_code_count p fid yes +
            cm_stmt_code_count p fid no)] ++
        cm_emit_stmt p fid
          (pc + 2i + cm_stmt_code_count p fid yes)
          owner breakpc continuepc no) &&
     (!p fid pc temp owner breakpc continuepc guard body
         loop_start loop_end.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
             (loop_start:int) (loop_end:int)) =
        [TVMInst TVMJzOp loop_end] ++
        cm_emit_stmt p fid (pc + 1i) owner loop_end loop_start body ++
        [TVMInst TVMJmpOp loop_start]) &&
     (!p fid pc temp owner breakpc continuepc guard body env regions
         loop_start loop_end.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
             (env:int->int->cm_value) (regions:(cm_region)list)
             (loop_start:int) (loop_end:int)) =
        [TVMInst TVMJmpOp loop_start]) &&
     (!p fid pc temp owner breakpc continuepc.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          CAReturnP = cm_return_tail_code p fid) &&
     (!p fid pc temp owner breakpc continuepc callee rest values ret
         all_args base_slot current_slot scratch.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          (CAArgP (callee:int) (rest:(cm_expr)list)
             (values:(cm_value)list) (ret:cm_type)
             (all_args:(cm_expr)list) (base_slot:int)
             (current_slot:int) (scratch:int)) =
        cm_temp_store_code p fid current_slot ++
        cm_emit_args_store p fid
          (pc + ilength (cm_temp_store_code p fid current_slot))
          (current_slot + 1i) scratch rest ++
        cm_emit_args_reload p fid base_slot all_args ++
        [TVMInst TVMCallOp (cm_function_pc p callee)]) &&
     (!p fid pc temp owner breakpc continuepc caller env fp regions ret.
        cm_value_phase_code p fid pc temp owner breakpc continuepc
          (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
             (regions:(cm_region)list) (ret:cm_type)) =
        cm_return_tail_code p fid)`);

PROOF thm cm_phase_is_call_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(cm_phase_is_call CAHaltP = F) &&
     (!ty. cm_phase_is_call (CALoadP (ty:cm_type)) = F) &&
     (!src ty. cm_phase_is_call (CAAssignLP (src:cm_expr) (ty:cm_type)) = F) &&
     (!ptr ty. cm_phase_is_call (CAAssignRP (ptr:cm_value) (ty:cm_type)) = F) &&
     (!op left right ty. cm_phase_is_call (CABinLP (op:int) (left:cm_expr) (right:cm_expr) (ty:cm_type)) = F) &&
     (!op left right value ty. cm_phase_is_call (CABinRP (op:int) (left:cm_expr) (right:cm_expr) (value:cm_value) (ty:cm_type)) = F) &&
     (!op. cm_phase_is_call (CAUnaryP (op:int)) = F) &&
     (!index ty. cm_phase_is_call (CAIndexLP (index:cm_expr) (ty:cm_type)) = F) &&
     (!base ty. cm_phase_is_call (CAIndexRP (base:cm_value) (ty:cm_type)) = F) &&
     (!mid base_ty. cm_phase_is_call (CAMemberP (mid:int) (base_ty:cm_type)) = F) &&
     (cm_phase_is_call CAPutcP = F) &&
     (cm_phase_is_call CAPutiP = F) &&
     (cm_phase_is_call CAExitP = F) &&
     (cm_phase_is_call CAExprStmtP = F) &&
     (!slot. cm_phase_is_call (CAInitP (slot:int)) = F) &&
     (!env regions jump target. cm_phase_is_call (CABlockP (env:int->int->cm_value) (regions:(cm_region)list) (jump:bool) (target:int)) = F) &&
     (!second. cm_phase_is_call (CASeqP (second:cm_stmt)) = F) &&
     (!yes no. cm_phase_is_call (CAIfP (yes:cm_stmt) (no:cm_stmt)) = F) &&
     (!guard body loop_start loop_end. cm_phase_is_call (CAWhileGuardP (guard:cm_expr) (body:cm_stmt) (loop_start:int) (loop_end:int)) = F) &&
     (!guard body env regions loop_start loop_end. cm_phase_is_call (CAWhileBodyP (guard:cm_expr) (body:cm_stmt) (env:int->int->cm_value) (regions:(cm_region)list) (loop_start:int) (loop_end:int)) = F) &&
     (cm_phase_is_call CAReturnP = F) &&
     (!callee rest values ret all_args base_slot current_slot scratch. cm_phase_is_call (CAArgP (callee:int) (rest:(cm_expr)list) (values:(cm_value)list) (ret:cm_type) (all_args:(cm_expr)list) (base_slot:int) (current_slot:int) (scratch:int)) = F) &&
     (!caller env fp regions ret. cm_phase_is_call (CACallP (caller:int) (env:int->int->cm_value) (fp:int) (regions:(cm_region)list) (ret:cm_type)) = T)`);

PROOF thm cm_phase_caller_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(cm_phase_caller CAHaltP = --1i) &&
     (!ty. cm_phase_caller (CALoadP (ty:cm_type)) = --1i) &&
     (!src ty. cm_phase_caller (CAAssignLP (src:cm_expr) (ty:cm_type)) = --1i) &&
     (!ptr ty. cm_phase_caller (CAAssignRP (ptr:cm_value) (ty:cm_type)) = --1i) &&
     (!op left right ty. cm_phase_caller (CABinLP (op:int) (left:cm_expr) (right:cm_expr) (ty:cm_type)) = --1i) &&
     (!op left right value ty. cm_phase_caller (CABinRP (op:int) (left:cm_expr) (right:cm_expr) (value:cm_value) (ty:cm_type)) = --1i) &&
     (!op. cm_phase_caller (CAUnaryP (op:int)) = --1i) &&
     (!index ty. cm_phase_caller (CAIndexLP (index:cm_expr) (ty:cm_type)) = --1i) &&
     (!base ty. cm_phase_caller (CAIndexRP (base:cm_value) (ty:cm_type)) = --1i) &&
     (!mid base_ty. cm_phase_caller (CAMemberP (mid:int) (base_ty:cm_type)) = --1i) &&
     (cm_phase_caller CAPutcP = --1i) &&
     (cm_phase_caller CAPutiP = --1i) &&
     (cm_phase_caller CAExitP = --1i) &&
     (cm_phase_caller CAExprStmtP = --1i) &&
     (!slot. cm_phase_caller (CAInitP (slot:int)) = --1i) &&
     (!env regions jump target. cm_phase_caller (CABlockP (env:int->int->cm_value) (regions:(cm_region)list) (jump:bool) (target:int)) = --1i) &&
     (!second. cm_phase_caller (CASeqP (second:cm_stmt)) = --1i) &&
     (!yes no. cm_phase_caller (CAIfP (yes:cm_stmt) (no:cm_stmt)) = --1i) &&
     (!guard body loop_start loop_end. cm_phase_caller (CAWhileGuardP (guard:cm_expr) (body:cm_stmt) (loop_start:int) (loop_end:int)) = --1i) &&
     (!guard body env regions loop_start loop_end. cm_phase_caller (CAWhileBodyP (guard:cm_expr) (body:cm_stmt) (env:int->int->cm_value) (regions:(cm_region)list) (loop_start:int) (loop_end:int)) = --1i) &&
     (cm_phase_caller CAReturnP = --1i) &&
     (!callee rest values ret all_args base_slot current_slot scratch. cm_phase_caller (CAArgP (callee:int) (rest:(cm_expr)list) (values:(cm_value)list) (ret:cm_type) (all_args:(cm_expr)list) (base_slot:int) (current_slot:int) (scratch:int)) = --1i) &&
     (!caller env fp regions ret. cm_phase_caller (CACallP (caller:int) (env:int->int->cm_value) (fp:int) (regions:(cm_region)list) (ret:cm_type)) = caller)`);

PROOF thm cm_phase_stops_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(cm_phase_stops CAHaltP = T) &&
     (!ty. cm_phase_stops (CALoadP (ty:cm_type)) = F) &&
     (!src ty. cm_phase_stops (CAAssignLP (src:cm_expr) (ty:cm_type)) = F) &&
     (!ptr ty. cm_phase_stops (CAAssignRP (ptr:cm_value) (ty:cm_type)) = F) &&
     (!op left right ty. cm_phase_stops (CABinLP (op:int) (left:cm_expr) (right:cm_expr) (ty:cm_type)) = F) &&
     (!op left right value ty. cm_phase_stops (CABinRP (op:int) (left:cm_expr) (right:cm_expr) (value:cm_value) (ty:cm_type)) = F) &&
     (!op. cm_phase_stops (CAUnaryP (op:int)) = F) &&
     (!index ty. cm_phase_stops (CAIndexLP (index:cm_expr) (ty:cm_type)) = F) &&
     (!base ty. cm_phase_stops (CAIndexRP (base:cm_value) (ty:cm_type)) = F) &&
     (!mid base_ty. cm_phase_stops (CAMemberP (mid:int) (base_ty:cm_type)) = F) &&
     (cm_phase_stops CAPutcP = F) &&
     (cm_phase_stops CAPutiP = F) &&
     (cm_phase_stops CAExitP = T) &&
     (cm_phase_stops CAExprStmtP = F) &&
     (!slot. cm_phase_stops (CAInitP (slot:int)) = F) &&
     (!env regions jump target. cm_phase_stops (CABlockP (env:int->int->cm_value) (regions:(cm_region)list) (jump:bool) (target:int)) = jump) &&
     (!second. cm_phase_stops (CASeqP (second:cm_stmt)) = F) &&
     (!yes no. cm_phase_stops (CAIfP (yes:cm_stmt) (no:cm_stmt)) = F) &&
     (!guard body loop_start loop_end. cm_phase_stops (CAWhileGuardP (guard:cm_expr) (body:cm_stmt) (loop_start:int) (loop_end:int)) = F) &&
     (!guard body env regions loop_start loop_end. cm_phase_stops (CAWhileBodyP (guard:cm_expr) (body:cm_stmt) (env:int->int->cm_value) (regions:(cm_region)list) (loop_start:int) (loop_end:int)) = F) &&
     (cm_phase_stops CAReturnP = T) &&
     (!callee rest values ret all_args base_slot current_slot scratch. cm_phase_stops (CAArgP (callee:int) (rest:(cm_expr)list) (values:(cm_value)list) (ret:cm_type) (all_args:(cm_expr)list) (base_slot:int) (current_slot:int) (scratch:int)) = F) &&
     (!caller env fp regions ret. cm_phase_stops (CACallP (caller:int) (env:int->int->cm_value) (fp:int) (regions:(cm_region)list) (ret:cm_type)) = T)`);

PROOF thm cm_phase_yields_normal_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(cm_phase_yields_normal CAHaltP = F) &&
     (!ty. cm_phase_yields_normal (CALoadP (ty:cm_type)) = F) &&
     (!src ty. cm_phase_yields_normal (CAAssignLP (src:cm_expr) (ty:cm_type)) = F) &&
     (!ptr ty. cm_phase_yields_normal (CAAssignRP (ptr:cm_value) (ty:cm_type)) = F) &&
     (!op left right ty. cm_phase_yields_normal (CABinLP (op:int) (left:cm_expr) (right:cm_expr) (ty:cm_type)) = F) &&
     (!op left right value ty. cm_phase_yields_normal (CABinRP (op:int) (left:cm_expr) (right:cm_expr) (value:cm_value) (ty:cm_type)) = F) &&
     (!op. cm_phase_yields_normal (CAUnaryP (op:int)) = F) &&
     (!index ty. cm_phase_yields_normal (CAIndexLP (index:cm_expr) (ty:cm_type)) = F) &&
     (!base ty. cm_phase_yields_normal (CAIndexRP (base:cm_value) (ty:cm_type)) = F) &&
     (!mid base_ty. cm_phase_yields_normal (CAMemberP (mid:int) (base_ty:cm_type)) = F) &&
     (cm_phase_yields_normal CAPutcP = F) &&
     (cm_phase_yields_normal CAPutiP = F) &&
     (cm_phase_yields_normal CAExitP = F) &&
     (cm_phase_yields_normal CAExprStmtP = T) &&
     (!slot. cm_phase_yields_normal (CAInitP (slot:int)) = T) &&
     (!env regions jump target. cm_phase_yields_normal (CABlockP (env:int->int->cm_value) (regions:(cm_region)list) (jump:bool) (target:int)) = T) &&
     (!second. cm_phase_yields_normal (CASeqP (second:cm_stmt)) = T) &&
     (!yes no. cm_phase_yields_normal (CAIfP (yes:cm_stmt) (no:cm_stmt)) = T) &&
     (!guard body loop_start loop_end. cm_phase_yields_normal (CAWhileGuardP (guard:cm_expr) (body:cm_stmt) (loop_start:int) (loop_end:int)) = T) &&
     (!guard body env regions loop_start loop_end. cm_phase_yields_normal (CAWhileBodyP (guard:cm_expr) (body:cm_stmt) (env:int->int->cm_value) (regions:(cm_region)list) (loop_start:int) (loop_end:int)) = T) &&
     (cm_phase_yields_normal CAReturnP = F) &&
     (!callee rest values ret all_args base_slot current_slot scratch. cm_phase_yields_normal (CAArgP (callee:int) (rest:(cm_expr)list) (values:(cm_value)list) (ret:cm_type) (all_args:(cm_expr)list) (base_slot:int) (current_slot:int) (scratch:int)) = F) &&
     (!caller env fp regions ret. cm_phase_yields_normal (CACallP (caller:int) (env:int->int->cm_value) (fp:int) (regions:(cm_region)list) (ret:cm_type)) = F)`);

PROOF thm cm_normal_phase_code_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(!p fid pc temp owner breakpc continuepc.
        cm_normal_phase_code (p:cm_program) (fid:int) (pc:int)
          (temp:int) (owner:int) (breakpc:int) (continuepc:int)
          CAHaltP = []) &&
     (!p fid pc temp owner breakpc continuepc ty. cm_normal_phase_code p fid pc temp owner breakpc continuepc (CALoadP (ty:cm_type)) = []) &&
     (!p fid pc temp owner breakpc continuepc src ty. cm_normal_phase_code p fid pc temp owner breakpc continuepc (CAAssignLP (src:cm_expr) (ty:cm_type)) = []) &&
     (!p fid pc temp owner breakpc continuepc ptr ty. cm_normal_phase_code p fid pc temp owner breakpc continuepc (CAAssignRP (ptr:cm_value) (ty:cm_type)) = []) &&
     (!p fid pc temp owner breakpc continuepc op left right ty. cm_normal_phase_code p fid pc temp owner breakpc continuepc (CABinLP (op:int) (left:cm_expr) (right:cm_expr) (ty:cm_type)) = []) &&
     (!p fid pc temp owner breakpc continuepc op left right value ty. cm_normal_phase_code p fid pc temp owner breakpc continuepc (CABinRP (op:int) (left:cm_expr) (right:cm_expr) (value:cm_value) (ty:cm_type)) = []) &&
     (!p fid pc temp owner breakpc continuepc op. cm_normal_phase_code p fid pc temp owner breakpc continuepc (CAUnaryP (op:int)) = []) &&
     (!p fid pc temp owner breakpc continuepc index ty. cm_normal_phase_code p fid pc temp owner breakpc continuepc (CAIndexLP (index:cm_expr) (ty:cm_type)) = []) &&
     (!p fid pc temp owner breakpc continuepc base ty. cm_normal_phase_code p fid pc temp owner breakpc continuepc (CAIndexRP (base:cm_value) (ty:cm_type)) = []) &&
     (!p fid pc temp owner breakpc continuepc mid base_ty. cm_normal_phase_code p fid pc temp owner breakpc continuepc (CAMemberP (mid:int) (base_ty:cm_type)) = []) &&
     (!p fid pc temp owner breakpc continuepc. cm_normal_phase_code p fid pc temp owner breakpc continuepc CAPutcP = []) &&
     (!p fid pc temp owner breakpc continuepc. cm_normal_phase_code p fid pc temp owner breakpc continuepc CAPutiP = []) &&
     (!p fid pc temp owner breakpc continuepc. cm_normal_phase_code p fid pc temp owner breakpc continuepc CAExitP = []) &&
     (!p fid pc temp owner breakpc continuepc. cm_normal_phase_code p fid pc temp owner breakpc continuepc CAExprStmtP = []) &&
     (!p fid pc temp owner breakpc continuepc slot. cm_normal_phase_code p fid pc temp owner breakpc continuepc (CAInitP (slot:int)) = []) &&
     (!p fid pc temp owner breakpc continuepc env regions jump target.
        cm_normal_phase_code p fid pc temp owner breakpc continuepc
          (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
            (jump:bool) (target:int)) =
        (if jump then [TVMInst TVMJmpOp target] else [])) &&
     (!p fid pc temp owner breakpc continuepc second.
        cm_normal_phase_code p fid pc temp owner breakpc continuepc
          (CASeqP (second:cm_stmt)) =
        cm_emit_stmt p fid pc owner breakpc continuepc second) &&
     (!p fid pc temp owner breakpc continuepc yes no. cm_normal_phase_code p fid pc temp owner breakpc continuepc (CAIfP (yes:cm_stmt) (no:cm_stmt)) = []) &&
     (!p fid pc temp owner breakpc continuepc guard body loop_start loop_end. cm_normal_phase_code p fid pc temp owner breakpc continuepc (CAWhileGuardP (guard:cm_expr) (body:cm_stmt) (loop_start:int) (loop_end:int)) = []) &&
     (!p fid pc temp owner breakpc continuepc guard body env regions loop_start loop_end.
        cm_normal_phase_code p fid pc temp owner breakpc continuepc
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
            (env:int->int->cm_value) (regions:(cm_region)list)
            (loop_start:int) (loop_end:int)) =
        [TVMInst TVMJmpOp loop_start]) &&
     (!p fid pc temp owner breakpc continuepc. cm_normal_phase_code p fid pc temp owner breakpc continuepc CAReturnP = []) &&
     (!p fid pc temp owner breakpc continuepc callee rest values ret all_args base_slot current_slot scratch. cm_normal_phase_code p fid pc temp owner breakpc continuepc (CAArgP (callee:int) (rest:(cm_expr)list) (values:(cm_value)list) (ret:cm_type) (all_args:(cm_expr)list) (base_slot:int) (current_slot:int) (scratch:int)) = []) &&
     (!p fid pc temp owner breakpc continuepc caller env fp regions ret.
        cm_normal_phase_code p fid pc temp owner breakpc continuepc
          (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
            (regions:(cm_region)list) (ret:cm_type)) =
        cm_fallthrough_tail_code)`);

PROOF thm cm_normal_phase_stops_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(cm_normal_phase_stops CAHaltP = T) &&
     (!ty. cm_normal_phase_stops (CALoadP (ty:cm_type)) = F) &&
     (!src ty. cm_normal_phase_stops (CAAssignLP (src:cm_expr) (ty:cm_type)) = F) &&
     (!ptr ty. cm_normal_phase_stops (CAAssignRP (ptr:cm_value) (ty:cm_type)) = F) &&
     (!op left right ty. cm_normal_phase_stops (CABinLP (op:int) (left:cm_expr) (right:cm_expr) (ty:cm_type)) = F) &&
     (!op left right value ty. cm_normal_phase_stops (CABinRP (op:int) (left:cm_expr) (right:cm_expr) (value:cm_value) (ty:cm_type)) = F) &&
     (!op. cm_normal_phase_stops (CAUnaryP (op:int)) = F) &&
     (!index ty. cm_normal_phase_stops (CAIndexLP (index:cm_expr) (ty:cm_type)) = F) &&
     (!base ty. cm_normal_phase_stops (CAIndexRP (base:cm_value) (ty:cm_type)) = F) &&
     (!mid base_ty. cm_normal_phase_stops (CAMemberP (mid:int) (base_ty:cm_type)) = F) &&
     (cm_normal_phase_stops CAPutcP = F) &&
     (cm_normal_phase_stops CAPutiP = F) &&
     (cm_normal_phase_stops CAExitP = T) &&
     (cm_normal_phase_stops CAExprStmtP = F) &&
     (!slot. cm_normal_phase_stops (CAInitP (slot:int)) = F) &&
     (!env regions jump target. cm_normal_phase_stops (CABlockP (env:int->int->cm_value) (regions:(cm_region)list) (jump:bool) (target:int)) = jump) &&
     (!second. cm_normal_phase_stops (CASeqP (second:cm_stmt)) = F) &&
     (!yes no. cm_normal_phase_stops (CAIfP (yes:cm_stmt) (no:cm_stmt)) = F) &&
     (!guard body loop_start loop_end. cm_normal_phase_stops (CAWhileGuardP (guard:cm_expr) (body:cm_stmt) (loop_start:int) (loop_end:int)) = F) &&
     (!guard body env regions loop_start loop_end. cm_normal_phase_stops (CAWhileBodyP (guard:cm_expr) (body:cm_stmt) (env:int->int->cm_value) (regions:(cm_region)list) (loop_start:int) (loop_end:int)) = F) &&
     (cm_normal_phase_stops CAReturnP = F) &&
     (!callee rest values ret all_args base_slot current_slot scratch. cm_normal_phase_stops (CAArgP (callee:int) (rest:(cm_expr)list) (values:(cm_value)list) (ret:cm_type) (all_args:(cm_expr)list) (base_slot:int) (current_slot:int) (scratch:int)) = F) &&
     (!caller env fp regions ret. cm_normal_phase_stops (CACallP (caller:int) (env:int->int->cm_value) (fp:int) (regions:(cm_region)list) (ret:cm_type)) = T)`);

PROOF thm cm_cursor_code_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid pc temp normal.
        cm_cursor_code (p:cm_program) (fid:int) (pc:int) (temp:int)
          (normal:bool) ([]:(cm_acursor)list) = []) &&
     (!p fid pc temp normal cursor rest.
        cm_cursor_code p fid pc temp normal
          ((cursor:cm_acursor) :: (rest:(cm_acursor)list)) =
        (if normal
         then cm_normal_phase_code p fid pc temp
           (cm_cursor_temp cursor) (cm_cursor_break cursor)
           (cm_cursor_continue cursor) (cm_cursor_phase cursor)
         else cm_value_phase_code p fid pc temp
           (cm_cursor_temp cursor) (cm_cursor_break cursor)
           (cm_cursor_continue cursor) (cm_cursor_phase cursor)) ++
        (if (if normal
             then cm_normal_phase_stops (cm_cursor_phase cursor)
             else cm_phase_stops (cm_cursor_phase cursor))
         then []
         else cm_cursor_code p fid
           (pc + ilength
             (if normal
              then cm_normal_phase_code p fid pc temp
                (cm_cursor_temp cursor) (cm_cursor_break cursor)
                (cm_cursor_continue cursor) (cm_cursor_phase cursor)
              else cm_value_phase_code p fid pc temp
                (cm_cursor_temp cursor) (cm_cursor_break cursor)
                (cm_cursor_continue cursor) (cm_cursor_phase cursor)))
           (cm_cursor_temp cursor)
           (normal || cm_phase_yields_normal (cm_cursor_phase cursor))
           rest))`);

PROOF thm cm_cont_code_def = new_fun_definition(
    `cm_cont_code (p:cm_program) (fid:int) (pc:int) (temp:int)
       (cursors:(cm_acursor)list) : (tvm_inst)list =
       cm_cursor_code p fid pc temp F cursors`);
PROOF thm cm_normal_cont_code_def = new_fun_definition(
    `cm_normal_cont_code (p:cm_program) (fid:int) (pc:int)
       (temp:int) (cursors:(cm_acursor)list) : (tvm_inst)list =
       cm_cursor_code p fid pc temp T cursors`);

PROOF thm cm_control_phase_code_def = new_fun_definition(
    `cm_control_phase_code (p:cm_program) (fid:int) (pc:int)
       (temp:int) (breakpc:int) (continuepc:int)
       (ctl:cm_control) (cursors:(cm_acursor)list) :
       (tvm_inst)list =
       (if cm_control_kind ctl == 3i
        then cm_return_tail_code p fid
        else if cm_control_kind ctl == 1i
        then [TVMInst TVMJmpOp breakpc]
        else if cm_control_kind ctl == 2i
        then [TVMInst TVMJmpOp continuepc]
        else if cm_control_kind ctl == 4i || cursors == []
        then []
        else cm_normal_cont_code p fid pc temp cursors)`);

PROOF thm cm_task_code_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!p q input ann.
        cm_task_code (p:cm_program)
          (CMStartTask (q:cm_program) (input:(int)list))
          (ann:cm_annotation) =
        [TVMInst TVMPushOp 1048576i;
         TVMInst TVMPushOp 8i; TVMInst TVMStoreOp 0i;
         TVMInst TVMCallOp (cm_function_pc p (cm_program_main p))]) &&
     (!p q fid expr st ks ann.
        cm_task_code p
          (CMRTask (q:cm_program) (fid:int) (expr:cm_expr)
             (st:cm_src_state) (ks:(cm_frame)list)) ann =
        cm_emit_rvalue p fid (cm_ann_pc ann) (cm_ann_temp ann) expr ++
        cm_cont_code p fid
          (cm_ann_pc ann + cm_rvalue_code_count p fid expr)
          (cm_ann_temp ann) (cm_ann_cursors ann)) &&
     (!p q fid expr st ks ann.
        cm_task_code p
          (CMLTask (q:cm_program) (fid:int) (expr:cm_expr)
             (st:cm_src_state) (ks:(cm_frame)list)) ann =
        cm_emit_lvalue p fid (cm_ann_pc ann) (cm_ann_temp ann) expr ++
        cm_cont_code p fid
          (cm_ann_pc ann + cm_lvalue_code_count p fid expr)
          (cm_ann_temp ann) (cm_ann_cursors ann)) &&
     (!p q fid stmt st ks ann.
        cm_task_code p
          (CMSTask (q:cm_program) (fid:int) (stmt:cm_stmt)
             (st:cm_src_state) (ks:(cm_frame)list)) ann =
        cm_emit_stmt p fid (cm_ann_pc ann) (cm_ann_temp ann)
          (cm_ann_break ann) (cm_ann_continue ann) stmt ++
        cm_normal_cont_code p fid
          (cm_ann_pc ann + cm_stmt_code_count p fid stmt)
          (cm_ann_temp ann) (cm_ann_cursors ann)) &&
     (!p q fid value st ks ann.
        cm_task_code p
          (CMVTask (q:cm_program) (fid:int) (value:cm_value)
             (st:cm_src_state) (ks:(cm_frame)list)) ann =
        cm_cont_code p fid (cm_ann_pc ann) (cm_ann_temp ann)
          (cm_ann_cursors ann)) &&
     (!p q fid ctl st ks ann.
        cm_task_code p
          (CMCTask (q:cm_program) (fid:int) (ctl:cm_control)
             (st:cm_src_state) (ks:(cm_frame)list)) ann =
        cm_control_phase_code p fid (cm_ann_pc ann)
          (cm_ann_temp ann) (cm_ann_break ann)
          (cm_ann_continue ann) ctl (cm_ann_cursors ann)) &&
     (!p st ctl status ann.
        cm_task_code (p:cm_program)
          (CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int))
          (ann:cm_annotation) = [])`);

PROOF thm cm_phase_site_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(!p code fid cursor rest calls. cm_phase_site (p:cm_program)
        (code:(tvm_inst)list) (fid:int) (cursor:cm_acursor)
        (rest:(cm_acursor)list) (calls:(cm_call_sim_frame)list)
        CAHaltP = T) &&
     (!p code fid cursor rest calls ty. cm_phase_site p code fid cursor rest calls (CALoadP (ty:cm_type)) = T) &&
     (!p code fid cursor rest calls src ty. cm_phase_site p code fid cursor rest calls (CAAssignLP (src:cm_expr) (ty:cm_type)) = T) &&
     (!p code fid cursor rest calls ptr ty. cm_phase_site p code fid cursor rest calls (CAAssignRP (ptr:cm_value) (ty:cm_type)) = T) &&
     (!p code fid cursor rest calls op left right ty. cm_phase_site p code fid cursor rest calls (CABinLP (op:int) (left:cm_expr) (right:cm_expr) (ty:cm_type)) = T) &&
     (!p code fid cursor rest calls op left right value ty. cm_phase_site p code fid cursor rest calls (CABinRP (op:int) (left:cm_expr) (right:cm_expr) (value:cm_value) (ty:cm_type)) = T) &&
     (!p code fid cursor rest calls op. cm_phase_site p code fid cursor rest calls (CAUnaryP (op:int)) = T) &&
     (!p code fid cursor rest calls index ty. cm_phase_site p code fid cursor rest calls (CAIndexLP (index:cm_expr) (ty:cm_type)) = T) &&
     (!p code fid cursor rest calls base ty. cm_phase_site p code fid cursor rest calls (CAIndexRP (base:cm_value) (ty:cm_type)) = T) &&
     (!p code fid cursor rest calls mid base_ty. cm_phase_site p code fid cursor rest calls (CAMemberP (mid:int) (base_ty:cm_type)) = T) &&
     (!p code fid cursor rest calls. cm_phase_site p code fid cursor rest calls CAPutcP = T) &&
     (!p code fid cursor rest calls. cm_phase_site p code fid cursor rest calls CAPutiP = T) &&
     (!p code fid cursor rest calls. cm_phase_site p code fid cursor rest calls CAExitP = T) &&
     (!p code fid cursor rest calls. cm_phase_site p code fid cursor rest calls CAExprStmtP = T) &&
     (!p code fid cursor rest calls slot. cm_phase_site p code fid cursor rest calls (CAInitP (slot:int)) = T) &&
     (!p code fid cursor rest calls env regions jump target.
        cm_phase_site p code fid cursor rest calls
          (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
             (jump:bool) (target:int)) =
        (~jump || cm_code_at code target
          (cm_normal_cont_code p fid target (cm_cursor_temp cursor) rest))) &&
     (!p code fid cursor rest calls second. cm_phase_site p code fid cursor rest calls (CASeqP (second:cm_stmt)) = T) &&
     (!p code fid cursor rest calls yes no. cm_phase_site p code fid cursor rest calls (CAIfP (yes:cm_stmt) (no:cm_stmt)) = T) &&
     (!p code fid cursor rest calls guard body loop_start loop_end.
        cm_phase_site p code fid cursor rest calls
          (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
             (loop_start:int) (loop_end:int)) =
        (cm_code_at code loop_start
           (cm_emit_rvalue p fid loop_start (cm_cursor_temp cursor) guard ++
            [TVMInst TVMJzOp loop_end] ++
            cm_emit_stmt p fid
              (loop_start + cm_rvalue_code_count p fid guard + 1i)
              (cm_cursor_temp cursor) loop_end loop_start body ++
            [TVMInst TVMJmpOp loop_start] ++
            cm_normal_cont_code p fid loop_end
              (cm_cursor_temp cursor) rest) &&
         cm_code_at code loop_end
           (cm_normal_cont_code p fid loop_end
             (cm_cursor_temp cursor) rest))) &&
     (!p code fid cursor rest calls guard body env regions loop_start loop_end.
        cm_phase_site p code fid cursor rest calls
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
             (env:int->int->cm_value) (regions:(cm_region)list)
             (loop_start:int) (loop_end:int)) =
        (cm_code_at code loop_start
           (cm_emit_rvalue p fid loop_start (cm_cursor_temp cursor) guard ++
            [TVMInst TVMJzOp loop_end] ++
            cm_emit_stmt p fid
              (loop_start + cm_rvalue_code_count p fid guard + 1i)
              (cm_cursor_temp cursor) loop_end loop_start body ++
            [TVMInst TVMJmpOp loop_start] ++
            cm_normal_cont_code p fid loop_end
              (cm_cursor_temp cursor) rest) &&
         cm_code_at code loop_end
           (cm_normal_cont_code p fid loop_end
             (cm_cursor_temp cursor) rest))) &&
     (!p code fid cursor rest calls. cm_phase_site p code fid cursor rest calls CAReturnP = T) &&
     (!p code fid cursor rest calls callee args values ret all_args base_slot current_slot scratch. cm_phase_site p code fid cursor rest calls (CAArgP (callee:int) (args:(cm_expr)list) (values:(cm_value)list) (ret:cm_type) (all_args:(cm_expr)list) (base_slot:int) (current_slot:int) (scratch:int)) = T) &&
     (!p code fid cursor rest calls caller env fp regions ret.
        cm_phase_site p code fid cursor rest calls
          (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
             (regions:(cm_region)list) (ret:cm_type)) =
        (~(calls == []) &&
         cm_code_at code (cm_call_sim_return (HD calls))
           (cm_cont_code p caller (cm_call_sim_return (HD calls))
             (cm_cursor_temp cursor) rest)))`);

PROOF thm cm_saved_layout_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p code fid calls.
        cm_saved_layout (p:cm_program) (code:(tvm_inst)list)
          (fid:int) ([]:(cm_acursor)list)
          (calls:(cm_call_sim_frame)list) = (calls == [])) &&
     (!p code fid cursor rest calls.
        cm_saved_layout p code fid
          ((cursor:cm_acursor) :: (rest:(cm_acursor)list)) calls =
        (cm_phase_site p code fid cursor rest calls
           (cm_cursor_phase cursor) &&
         cm_saved_layout p code
           (if cm_phase_is_call (cm_cursor_phase cursor)
            then cm_phase_caller (cm_cursor_phase cursor) else fid)
           rest
           (if cm_phase_is_call (cm_cursor_phase cursor)
            then TL calls else calls)))`);

PROOF thm cm_task_fid_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!p input. cm_task_fid
        (CMStartTask (p:cm_program) (input:(int)list)) = --1i) &&
     (!p fid expr st ks. cm_task_fid
        (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list)) = fid) &&
     (!p fid expr st ks. cm_task_fid
        (CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list)) = fid) &&
     (!p fid stmt st ks. cm_task_fid
        (CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
          (st:cm_src_state) (ks:(cm_frame)list)) = fid) &&
     (!p fid value st ks. cm_task_fid
        (CMVTask (p:cm_program) (fid:int) (value:cm_value)
          (st:cm_src_state) (ks:(cm_frame)list)) = fid) &&
     (!p fid ctl st ks. cm_task_fid
        (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
          (st:cm_src_state) (ks:(cm_frame)list)) = fid) &&
     (!st ctl status. cm_task_fid
        (CMDoneTask (st:cm_src_state) (ctl:cm_control)
          (status:int)) = --1i)`);

PROOF thm cm_task_layout_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!p q input ann.
        cm_task_layout (p:cm_program)
          (CMStartTask (q:cm_program) (input:(int)list))
          (ann:cm_annotation) =
        (cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (cm_task_code p (CMStartTask q input) ann) &&
         cm_saved_layout p (cm_model_code p)
           (cm_task_fid (CMStartTask q input))
           (cm_ann_cursors ann) (cm_ann_calls ann))) &&
     (!p q fid expr st ks ann.
        cm_task_layout p
          (CMRTask (q:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (cm_task_code p (CMRTask q fid expr st ks) ann) &&
         cm_saved_layout p (cm_model_code p)
           (cm_task_fid (CMRTask q fid expr st ks))
           (cm_ann_cursors ann) (cm_ann_calls ann))) &&
     (!p q fid expr st ks ann.
        cm_task_layout p
          (CMLTask (q:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (cm_task_code p (CMLTask q fid expr st ks) ann) &&
         cm_saved_layout p (cm_model_code p)
           (cm_task_fid (CMLTask q fid expr st ks))
           (cm_ann_cursors ann) (cm_ann_calls ann))) &&
     (!p q fid stmt st ks ann.
        cm_task_layout p
          (CMSTask (q:cm_program) (fid:int) (stmt:cm_stmt)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (cm_task_code p (CMSTask q fid stmt st ks) ann) &&
         cm_saved_layout p (cm_model_code p)
           (cm_task_fid (CMSTask q fid stmt st ks))
           (cm_ann_cursors ann) (cm_ann_calls ann))) &&
     (!p q fid v st ks ann.
        cm_task_layout p
          (CMVTask (q:cm_program) (fid:int) (v:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (cm_task_code p (CMVTask q fid v st ks) ann) &&
         cm_saved_layout p (cm_model_code p)
           (cm_task_fid (CMVTask q fid v st ks))
           (cm_ann_cursors ann) (cm_ann_calls ann))) &&
     (!p q fid ctl st ks ann.
        cm_task_layout p
          (CMCTask (q:cm_program) (fid:int) (ctl:cm_control)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (cm_task_code p (CMCTask q fid ctl st ks) ann) &&
         cm_saved_layout p (cm_model_code p)
           (cm_task_fid (CMCTask q fid ctl st ks))
           (cm_ann_cursors ann) (cm_ann_calls ann))) &&
     (!p st ctl status ann.
        cm_task_layout (p:cm_program)
          (CMDoneTask (st:cm_src_state) (ctl:cm_control)
            (status:int)) (ann:cm_annotation) = T)`);
PROOF static thm cm_prove_task_layout_done(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (ctl:cm_control)
         (status:int) (ann:cm_annotation).
         cm_task_layout p (CMDoneTask st ctl status) ann`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_task_layout_def)));
  return gnode_prove(root);
}
PROOF thm cm_task_layout_done = cm_prove_task_layout_done();

PROOF static thm cm_prove_task_layout_initial(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         cm_task_layout p (CMStartTask p input)
           cm_initial_annotation`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm prelude = spec_rule(`p:cm_program`, cm_model_prelude_at);
  thm prefix_rule = ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`, `0i:int`,
      `[TVMInst TVMPushOp 1048576i;
        TVMInst TVMPushOp 8i; TVMInst TVMStoreOp 0i;
        TVMInst TVMCallOp
          (cm_function_pc (p:cm_program) (cm_program_main p))]:
          (tvm_inst)list`,
      `[TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMAddOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMHaltOp 0i]:(tvm_inst)list`),
      cm_code_at_append_left);
  thm reduced_rule = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("APPEND"))), prefix_rule);
  thm reduced_prelude = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_emit_prelude_def())), prelude);
  thm prefix = mp_rule(reduced_rule, reduced_prelude);
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_task_layout_def, get_cm_task_done_def(),
      cm_task_code_def, cm_task_fid_def, cm_initial_annotation_def,
      cm_ann_pc_def, cm_ann_cursors_def, cm_ann_calls_def)));
  gnode_list parts = CONJ_TAC(opened);
  ACCEPT_TAC(parts[0], prefix);
  CONV_TAC(parts[1], reduce_rewrite_conv(THM_LIST(
      cm_saved_layout_def)));
  return gnode_prove(root);
}
PROOF thm cm_task_layout_initial = cm_prove_task_layout_initial();

PROOF thm get_cm_task_layout_initial(void) {
  return cm_task_layout_initial;
}
PROOF thm get_cm_task_layout_done(void) {
  return cm_task_layout_done;
}

PROOF int _e_cm_value_phase_code =
    cst_add_const_to_header(`cm_value_phase_code`);
PROOF int _e_cm_normal_phase_code =
    cst_add_const_to_header(`cm_normal_phase_code`);
PROOF int _e_cm_cursor_code = cst_add_const_to_header(`cm_cursor_code`);
PROOF int _e_cm_cont_code = cst_add_const_to_header(`cm_cont_code`);
PROOF int _e_cm_normal_cont_code =
    cst_add_const_to_header(`cm_normal_cont_code`);
PROOF int _e_cm_phase_is_call =
    cst_add_const_to_header(`cm_phase_is_call`);
PROOF int _e_cm_phase_caller =
    cst_add_const_to_header(`cm_phase_caller`);
PROOF int _e_cm_phase_stops =
    cst_add_const_to_header(`cm_phase_stops`);
PROOF int _e_cm_phase_yields_normal =
    cst_add_const_to_header(`cm_phase_yields_normal`);
PROOF int _e_cm_normal_phase_stops =
    cst_add_const_to_header(`cm_normal_phase_stops`);
PROOF int _e_cm_phase_site = cst_add_const_to_header(`cm_phase_site`);
PROOF int _e_cm_control_phase_code =
    cst_add_const_to_header(`cm_control_phase_code`);
PROOF int _e_cm_task_code = cst_add_const_to_header(`cm_task_code`);
PROOF int _e_cm_task_fid = cst_add_const_to_header(`cm_task_fid`);
PROOF int _e_cm_saved_layout = cst_add_const_to_header(`cm_saved_layout`);
PROOF int _e_cm_task_layout = cst_add_const_to_header(`cm_task_layout`);

PROOF static int cmc_preservation_code_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_code_axioms_before,
      "cmc_preservation_code introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_code_checks =
    cmc_preservation_code_final_checks();
