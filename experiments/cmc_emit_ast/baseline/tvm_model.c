#include "proof/proof.h"
#include "userlib/renderers.h"
#include "tower_base.h"
#require "tower_base.c"
#include "tvm_model.h"
#include "userlib/proof.h"

PROOF static size_t _tvm_axioms_before = vector_size(get_all_axioms());

PROOF indtype tvm_opcode_ty = new_datatype_definition(
    "tvm_opcode = TVMPushOp | TVMPopOp | TVMDupOp | TVMSwapOp"
    " | TVMLoadOp | TVMStoreOp | TVMLoadBOp | TVMStoreBOp"
    " | TVMAddOp | TVMSubOp | TVMMulOp | TVMDivOp | TVMModOp"
    " | TVMEqOp | TVMNeOp | TVMLtOp | TVMLeOp | TVMGtOp | TVMGeOp"
    " | TVMJmpOp | TVMJzOp | TVMJnzOp | TVMCallOp | TVMRetOp"
    " | TVMGetcOp | TVMPutcOp | TVMPutiOp | TVMHaltOp");
PROOF thm tvm_opcode_RECURSION = tvm_opcode_ty.rec;
PROOF static int _t_tvm_opcode = cst_add_type_to_header("tvm_opcode", 0);
PROOF static int _c_TVMPushOp =
    cst_add_const_to_header(`TVMPushOp:tvm_opcode`);
PROOF static int _c_TVMPopOp =
    cst_add_const_to_header(`TVMPopOp:tvm_opcode`);
PROOF static int _c_TVMDupOp =
    cst_add_const_to_header(`TVMDupOp:tvm_opcode`);
PROOF static int _c_TVMSwapOp =
    cst_add_const_to_header(`TVMSwapOp:tvm_opcode`);
PROOF static int _c_TVMLoadOp =
    cst_add_const_to_header(`TVMLoadOp:tvm_opcode`);
PROOF static int _c_TVMStoreOp =
    cst_add_const_to_header(`TVMStoreOp:tvm_opcode`);
PROOF static int _c_TVMLoadBOp =
    cst_add_const_to_header(`TVMLoadBOp:tvm_opcode`);
PROOF static int _c_TVMStoreBOp =
    cst_add_const_to_header(`TVMStoreBOp:tvm_opcode`);
PROOF static int _c_TVMAddOp =
    cst_add_const_to_header(`TVMAddOp:tvm_opcode`);
PROOF static int _c_TVMSubOp =
    cst_add_const_to_header(`TVMSubOp:tvm_opcode`);
PROOF static int _c_TVMMulOp =
    cst_add_const_to_header(`TVMMulOp:tvm_opcode`);
PROOF static int _c_TVMDivOp =
    cst_add_const_to_header(`TVMDivOp:tvm_opcode`);
PROOF static int _c_TVMModOp =
    cst_add_const_to_header(`TVMModOp:tvm_opcode`);
PROOF static int _c_TVMEqOp =
    cst_add_const_to_header(`TVMEqOp:tvm_opcode`);
PROOF static int _c_TVMNeOp =
    cst_add_const_to_header(`TVMNeOp:tvm_opcode`);
PROOF static int _c_TVMLtOp =
    cst_add_const_to_header(`TVMLtOp:tvm_opcode`);
PROOF static int _c_TVMLeOp =
    cst_add_const_to_header(`TVMLeOp:tvm_opcode`);
PROOF static int _c_TVMGtOp =
    cst_add_const_to_header(`TVMGtOp:tvm_opcode`);
PROOF static int _c_TVMGeOp =
    cst_add_const_to_header(`TVMGeOp:tvm_opcode`);
PROOF static int _c_TVMJmpOp =
    cst_add_const_to_header(`TVMJmpOp:tvm_opcode`);
PROOF static int _c_TVMJzOp =
    cst_add_const_to_header(`TVMJzOp:tvm_opcode`);
PROOF static int _c_TVMJnzOp =
    cst_add_const_to_header(`TVMJnzOp:tvm_opcode`);
PROOF static int _c_TVMCallOp =
    cst_add_const_to_header(`TVMCallOp:tvm_opcode`);
PROOF static int _c_TVMRetOp =
    cst_add_const_to_header(`TVMRetOp:tvm_opcode`);
PROOF static int _c_TVMGetcOp =
    cst_add_const_to_header(`TVMGetcOp:tvm_opcode`);
PROOF static int _c_TVMPutcOp =
    cst_add_const_to_header(`TVMPutcOp:tvm_opcode`);
PROOF static int _c_TVMPutiOp =
    cst_add_const_to_header(`TVMPutiOp:tvm_opcode`);
PROOF static int _c_TVMHaltOp =
    cst_add_const_to_header(`TVMHaltOp:tvm_opcode`);

PROOF thm tvm_opcode_code_def = new_rec_definition(
    tvm_opcode_RECURSION,
    `(tvm_opcode_code TVMPushOp = 0i) &&
     (tvm_opcode_code TVMPopOp = 1i) &&
     (tvm_opcode_code TVMDupOp = 2i) &&
     (tvm_opcode_code TVMSwapOp = 3i) &&
     (tvm_opcode_code TVMLoadOp = 4i) &&
     (tvm_opcode_code TVMStoreOp = 5i) &&
     (tvm_opcode_code TVMLoadBOp = 6i) &&
     (tvm_opcode_code TVMStoreBOp = 7i) &&
     (tvm_opcode_code TVMAddOp = 8i) &&
     (tvm_opcode_code TVMSubOp = 9i) &&
     (tvm_opcode_code TVMMulOp = 10i) &&
     (tvm_opcode_code TVMDivOp = 11i) &&
     (tvm_opcode_code TVMModOp = 12i) &&
     (tvm_opcode_code TVMEqOp = 13i) &&
     (tvm_opcode_code TVMNeOp = 14i) &&
     (tvm_opcode_code TVMLtOp = 15i) &&
     (tvm_opcode_code TVMLeOp = 16i) &&
     (tvm_opcode_code TVMGtOp = 17i) &&
     (tvm_opcode_code TVMGeOp = 18i) &&
     (tvm_opcode_code TVMJmpOp = 19i) &&
     (tvm_opcode_code TVMJzOp = 20i) &&
     (tvm_opcode_code TVMJnzOp = 21i) &&
     (tvm_opcode_code TVMCallOp = 22i) &&
     (tvm_opcode_code TVMRetOp = 23i) &&
     (tvm_opcode_code TVMGetcOp = 24i) &&
     (tvm_opcode_code TVMPutcOp = 25i) &&
     (tvm_opcode_code TVMPutiOp = 26i) &&
     (tvm_opcode_code TVMHaltOp = 27i)`);
PROOF int _e_tvm_opcode_code =
    cst_add_const_to_header(`tvm_opcode_code`);

PROOF thm tvm_opcode_decode_def = new_fun_definition(
    `tvm_opcode_decode (code:int) : tvm_opcode =
       (if code == 0i then TVMPushOp
        else if code == 1i then TVMPopOp
        else if code == 2i then TVMDupOp
        else if code == 3i then TVMSwapOp
        else if code == 4i then TVMLoadOp
        else if code == 5i then TVMStoreOp
        else if code == 6i then TVMLoadBOp
        else if code == 7i then TVMStoreBOp
        else if code == 8i then TVMAddOp
        else if code == 9i then TVMSubOp
        else if code == 10i then TVMMulOp
        else if code == 11i then TVMDivOp
        else if code == 12i then TVMModOp
        else if code == 13i then TVMEqOp
        else if code == 14i then TVMNeOp
        else if code == 15i then TVMLtOp
        else if code == 16i then TVMLeOp
        else if code == 17i then TVMGtOp
        else if code == 18i then TVMGeOp
        else if code == 19i then TVMJmpOp
        else if code == 20i then TVMJzOp
        else if code == 21i then TVMJnzOp
        else if code == 22i then TVMCallOp
        else if code == 23i then TVMRetOp
        else if code == 24i then TVMGetcOp
        else if code == 25i then TVMPutcOp
        else if code == 26i then TVMPutiOp
        else TVMHaltOp)`);
PROOF int _e_tvm_opcode_decode =
    cst_add_const_to_header(`tvm_opcode_decode`);

PROOF thm mk_tvm_opcode_roundtrip(void) {
  gnode root = gnode_new_with_ccl(
      `!(op:tvm_opcode).
         tvm_opcode_decode (tvm_opcode_code op) == op`);
  gnode_list cases = INDUCT_TAC(root, `op:tvm_opcode`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_TAC(cases[i], then_conv(
        rewrite_conv(THM_LIST(tvm_opcode_code_def, tvm_opcode_decode_def)),
        get_conversion_by_name("INT_REDUCE_CONV")));
  }
  return gnode_prove(root);
}
PROOF thm tvm_opcode_roundtrip = mk_tvm_opcode_roundtrip();

PROOF indtype tvm_inst_ty = new_datatype_definition(
    "tvm_inst = TVMInst tvm_opcode int");
PROOF indtype tvm_patch_ty = new_datatype_definition(
    "tvm_patch = TVMPatch int int");
PROOF indtype tvm_object_ty = new_datatype_definition(
    "tvm_object = TVMObject int (tvm_inst)list (tvm_patch)list");
PROOF indtype tvm_state_ty = new_datatype_definition(
    "tvm_state = TVMState int (int)list (int)list (int->int) "
    "(int)list (int)list");
PROOF indtype tvm_action_ty = new_datatype_definition(
    "tvm_action = TVMStepState tvm_state"
    " | TVMStepHalt tvm_state int | TVMStepError tvm_state");
PROOF indtype tvm_task_ty = new_datatype_definition(
    "tvm_task = TVMBoot tvm_object (int)list"
    " | TVMRunTask tvm_object tvm_state"
    " | TVMDoneTask tvm_state int int");
PROOF indtype tvm_outcome_ty = new_datatype_definition(
    "tvm_outcome = TVMOutcome tvm_state int int");

PROOF thm tvm_inst_RECURSION = tvm_inst_ty.rec;
PROOF thm tvm_patch_RECURSION = tvm_patch_ty.rec;
PROOF thm tvm_object_RECURSION = tvm_object_ty.rec;
PROOF thm tvm_state_RECURSION = tvm_state_ty.rec;
PROOF thm tvm_action_RECURSION = tvm_action_ty.rec;
PROOF thm tvm_task_RECURSION = tvm_task_ty.rec;
PROOF thm tvm_outcome_RECURSION = tvm_outcome_ty.rec;

PROOF static int _t_tvm_inst = cst_add_type_to_header("tvm_inst", 0);
PROOF static int _t_tvm_patch = cst_add_type_to_header("tvm_patch", 0);
PROOF static int _t_tvm_object = cst_add_type_to_header("tvm_object", 0);
PROOF static int _t_tvm_state = cst_add_type_to_header("tvm_state", 0);
PROOF static int _t_tvm_action = cst_add_type_to_header("tvm_action", 0);
PROOF static int _t_tvm_task = cst_add_type_to_header("tvm_task", 0);
PROOF static int _t_tvm_outcome = cst_add_type_to_header("tvm_outcome", 0);
PROOF static int _c_TVMInst =
    cst_add_const_to_header(`TVMInst:tvm_opcode->int->tvm_inst`);
PROOF static int _c_TVMPatch =
    cst_add_const_to_header(`TVMPatch:int->int->tvm_patch`);
PROOF static int _c_TVMObject = cst_add_const_to_header(
    `TVMObject:int->(tvm_inst)list->(tvm_patch)list->tvm_object`);
PROOF static int _c_TVMState = cst_add_const_to_header(
    `TVMState:int->(int)list->(int)list->(int->int)->
      (int)list->(int)list->tvm_state`);
PROOF static int _c_TVMStepState =
    cst_add_const_to_header(`TVMStepState:tvm_state->tvm_action`);
PROOF static int _c_TVMStepHalt =
    cst_add_const_to_header(`TVMStepHalt:tvm_state->int->tvm_action`);
PROOF static int _c_TVMStepError =
    cst_add_const_to_header(`TVMStepError:tvm_state->tvm_action`);
PROOF static int _c_TVMBoot =
    cst_add_const_to_header(`TVMBoot:tvm_object->(int)list->tvm_task`);
PROOF static int _c_TVMRunTask =
    cst_add_const_to_header(`TVMRunTask:tvm_object->tvm_state->tvm_task`);
PROOF static int _c_TVMDoneTask =
    cst_add_const_to_header(`TVMDoneTask:tvm_state->int->int->tvm_task`);
PROOF static int _c_TVMOutcome =
    cst_add_const_to_header(`TVMOutcome:tvm_state->int->int->tvm_outcome`);

/* Total selectors keep loader and execution equations first-order. */
PROOF thm tvm_inst_op_def = new_rec_definition(tvm_inst_RECURSION,
    `tvm_inst_op (TVMInst (op:tvm_opcode) (imm:int)) = op`);
PROOF thm tvm_inst_imm_def = new_rec_definition(tvm_inst_RECURSION,
    `tvm_inst_imm (TVMInst (op:tvm_opcode) (imm:int)) = imm`);
PROOF thm tvm_patch_addr_def = new_rec_definition(tvm_patch_RECURSION,
    `tvm_patch_addr (TVMPatch (addr:int) (byte:int)) = addr`);
PROOF thm tvm_patch_byte_def = new_rec_definition(tvm_patch_RECURSION,
    `tvm_patch_byte (TVMPatch (addr:int) (byte:int)) = byte`);
PROOF thm tvm_object_entry_def = new_rec_definition(tvm_object_RECURSION,
    `tvm_object_entry
       (TVMObject (entry:int) (code:(tvm_inst)list)
         (patches:(tvm_patch)list)) = entry`);
PROOF thm tvm_object_code_def = new_rec_definition(tvm_object_RECURSION,
    `tvm_object_code
       (TVMObject (entry:int) (code:(tvm_inst)list)
         (patches:(tvm_patch)list)) = code`);
PROOF thm tvm_object_patches_def = new_rec_definition(tvm_object_RECURSION,
    `tvm_object_patches
       (TVMObject (entry:int) (code:(tvm_inst)list)
         (patches:(tvm_patch)list)) = patches`);

PROOF thm tvm_pc_def = new_rec_definition(tvm_state_RECURSION,
    `tvm_pc
       (TVMState (pc:int) (stack:(int)list) (calls:(int)list)
         (mem:int->int) (input:(int)list) (output:(int)list)) = pc`);
PROOF thm tvm_stack_def = new_rec_definition(tvm_state_RECURSION,
    `tvm_stack
       (TVMState (pc:int) (stack:(int)list) (calls:(int)list)
         (mem:int->int) (input:(int)list) (output:(int)list)) = stack`);
PROOF thm tvm_calls_def = new_rec_definition(tvm_state_RECURSION,
    `tvm_calls
       (TVMState (pc:int) (stack:(int)list) (calls:(int)list)
         (mem:int->int) (input:(int)list) (output:(int)list)) = calls`);
PROOF thm tvm_mem_def = new_rec_definition(tvm_state_RECURSION,
    `tvm_mem
       (TVMState (pc:int) (stack:(int)list) (calls:(int)list)
         (mem:int->int) (input:(int)list) (output:(int)list)) = mem`);
PROOF thm tvm_input_def = new_rec_definition(tvm_state_RECURSION,
    `tvm_input
       (TVMState (pc:int) (stack:(int)list) (calls:(int)list)
         (mem:int->int) (input:(int)list) (output:(int)list)) = input`);
PROOF thm tvm_output_def = new_rec_definition(tvm_state_RECURSION,
    `tvm_output
       (TVMState (pc:int) (stack:(int)list) (calls:(int)list)
         (mem:int->int) (input:(int)list) (output:(int)list)) = output`);

PROOF thm tvm_action_kind_def = new_rec_definition(tvm_action_RECURSION,
    `(tvm_action_kind (TVMStepState (st:tvm_state)) = 0i) &&
     (!st status. tvm_action_kind
        (TVMStepHalt (st:tvm_state) (status:int)) = 1i) &&
     (!st. tvm_action_kind (TVMStepError (st:tvm_state)) = 2i)`);
PROOF thm tvm_action_state_def = new_rec_definition(tvm_action_RECURSION,
    `(tvm_action_state (TVMStepState (st:tvm_state)) = st) &&
     (!st status. tvm_action_state
        (TVMStepHalt (st:tvm_state) (status:int)) = st) &&
     (!st. tvm_action_state (TVMStepError (st:tvm_state)) = st)`);
PROOF thm tvm_action_status_def = new_rec_definition(tvm_action_RECURSION,
    `(tvm_action_status (TVMStepState (st:tvm_state)) = 0i) &&
     (!st status. tvm_action_status
        (TVMStepHalt (st:tvm_state) (status:int)) = status) &&
     (!st. tvm_action_status (TVMStepError (st:tvm_state)) = 2i)`);
PROOF thm tvm_outcome_state_def = new_rec_definition(tvm_outcome_RECURSION,
    `tvm_outcome_state
       (TVMOutcome (st:tvm_state) (status:int) (kind:int)) = st`);
PROOF thm tvm_outcome_status_def = new_rec_definition(tvm_outcome_RECURSION,
    `tvm_outcome_status
       (TVMOutcome (st:tvm_state) (status:int) (kind:int)) = status`);
PROOF thm tvm_outcome_kind_def = new_rec_definition(tvm_outcome_RECURSION,
    `tvm_outcome_kind
       (TVMOutcome (st:tvm_state) (status:int) (kind:int)) = kind`);

PROOF int _e_tvm_inst_op = cst_add_const_to_header(`tvm_inst_op`);
PROOF int _e_tvm_inst_imm = cst_add_const_to_header(`tvm_inst_imm`);
PROOF int _e_tvm_patch_addr = cst_add_const_to_header(`tvm_patch_addr`);
PROOF int _e_tvm_patch_byte = cst_add_const_to_header(`tvm_patch_byte`);
PROOF int _e_tvm_object_entry = cst_add_const_to_header(`tvm_object_entry`);
PROOF int _e_tvm_object_code = cst_add_const_to_header(`tvm_object_code`);
PROOF int _e_tvm_object_patches =
    cst_add_const_to_header(`tvm_object_patches`);
PROOF int _e_tvm_pc = cst_add_const_to_header(`tvm_pc`);
PROOF int _e_tvm_stack = cst_add_const_to_header(`tvm_stack`);
PROOF int _e_tvm_calls = cst_add_const_to_header(`tvm_calls`);
PROOF int _e_tvm_mem = cst_add_const_to_header(`tvm_mem`);
PROOF int _e_tvm_input = cst_add_const_to_header(`tvm_input`);
PROOF int _e_tvm_output = cst_add_const_to_header(`tvm_output`);
PROOF int _e_tvm_action_kind = cst_add_const_to_header(`tvm_action_kind`);
PROOF int _e_tvm_action_state = cst_add_const_to_header(`tvm_action_state`);
PROOF int _e_tvm_action_status =
    cst_add_const_to_header(`tvm_action_status`);
PROOF int _e_tvm_outcome_state =
    cst_add_const_to_header(`tvm_outcome_state`);
PROOF int _e_tvm_outcome_status =
    cst_add_const_to_header(`tvm_outcome_status`);
PROOF int _e_tvm_outcome_kind =
    cst_add_const_to_header(`tvm_outcome_kind`);

PROOF thm tvm_target_valid_def = new_fun_definition(
    `tvm_target_valid (code:(tvm_inst)list) (target:int) : bool =
       (0i <= target && target < ilength code)`);
PROOF thm tvm_opcode_has_imm_def = new_rec_definition(
    tvm_opcode_RECURSION,
    `(tvm_opcode_has_imm TVMPushOp = T) &&
     (tvm_opcode_has_imm TVMPopOp = F) &&
     (tvm_opcode_has_imm TVMDupOp = F) &&
     (tvm_opcode_has_imm TVMSwapOp = F) &&
     (tvm_opcode_has_imm TVMLoadOp = F) &&
     (tvm_opcode_has_imm TVMStoreOp = F) &&
     (tvm_opcode_has_imm TVMLoadBOp = F) &&
     (tvm_opcode_has_imm TVMStoreBOp = F) &&
     (tvm_opcode_has_imm TVMAddOp = F) &&
     (tvm_opcode_has_imm TVMSubOp = F) &&
     (tvm_opcode_has_imm TVMMulOp = F) &&
     (tvm_opcode_has_imm TVMDivOp = F) &&
     (tvm_opcode_has_imm TVMModOp = F) &&
     (tvm_opcode_has_imm TVMEqOp = F) &&
     (tvm_opcode_has_imm TVMNeOp = F) &&
     (tvm_opcode_has_imm TVMLtOp = F) &&
     (tvm_opcode_has_imm TVMLeOp = F) &&
     (tvm_opcode_has_imm TVMGtOp = F) &&
     (tvm_opcode_has_imm TVMGeOp = F) &&
     (tvm_opcode_has_imm TVMJmpOp = T) &&
     (tvm_opcode_has_imm TVMJzOp = T) &&
     (tvm_opcode_has_imm TVMJnzOp = T) &&
     (tvm_opcode_has_imm TVMCallOp = T) &&
     (tvm_opcode_has_imm TVMRetOp = F) &&
     (tvm_opcode_has_imm TVMGetcOp = F) &&
     (tvm_opcode_has_imm TVMPutcOp = F) &&
     (tvm_opcode_has_imm TVMPutiOp = F) &&
     (tvm_opcode_has_imm TVMHaltOp = F)`);
PROOF thm tvm_opcode_is_target_def = new_rec_definition(
    tvm_opcode_RECURSION,
    `(tvm_opcode_is_target TVMPushOp = F) &&
     (tvm_opcode_is_target TVMPopOp = F) &&
     (tvm_opcode_is_target TVMDupOp = F) &&
     (tvm_opcode_is_target TVMSwapOp = F) &&
     (tvm_opcode_is_target TVMLoadOp = F) &&
     (tvm_opcode_is_target TVMStoreOp = F) &&
     (tvm_opcode_is_target TVMLoadBOp = F) &&
     (tvm_opcode_is_target TVMStoreBOp = F) &&
     (tvm_opcode_is_target TVMAddOp = F) &&
     (tvm_opcode_is_target TVMSubOp = F) &&
     (tvm_opcode_is_target TVMMulOp = F) &&
     (tvm_opcode_is_target TVMDivOp = F) &&
     (tvm_opcode_is_target TVMModOp = F) &&
     (tvm_opcode_is_target TVMEqOp = F) &&
     (tvm_opcode_is_target TVMNeOp = F) &&
     (tvm_opcode_is_target TVMLtOp = F) &&
     (tvm_opcode_is_target TVMLeOp = F) &&
     (tvm_opcode_is_target TVMGtOp = F) &&
     (tvm_opcode_is_target TVMGeOp = F) &&
     (tvm_opcode_is_target TVMJmpOp = T) &&
     (tvm_opcode_is_target TVMJzOp = T) &&
     (tvm_opcode_is_target TVMJnzOp = T) &&
     (tvm_opcode_is_target TVMCallOp = T) &&
     (tvm_opcode_is_target TVMRetOp = F) &&
     (tvm_opcode_is_target TVMGetcOp = F) &&
     (tvm_opcode_is_target TVMPutcOp = F) &&
     (tvm_opcode_is_target TVMPutiOp = F) &&
     (tvm_opcode_is_target TVMHaltOp = F)`);
PROOF thm tvm_inst_shape_def = new_fun_definition(
    `tvm_inst_shape (inst:tvm_inst) : bool =
       (if tvm_opcode_has_imm (tvm_inst_op inst)
        then tower_signed64 (tvm_inst_imm inst)
        else tvm_inst_imm inst == 0i)`);
PROOF thm tvm_patch_valid_def = new_fun_definition(
    `tvm_patch_valid (patch:tvm_patch) : bool =
       (tower_addr_valid (tvm_patch_addr patch) &&
        tower_byte_value (tvm_patch_byte patch))`);
PROOF thm tvm_patches_valid_def = new_fun_definition(
    `tvm_patches_valid (patches:(tvm_patch)list) : bool =
       (!i. 0i <= i ==> i < ilength patches ==>
          tvm_patch_valid (inth i patches))`);
PROOF thm tvm_code_shape_def = new_fun_definition(
    `tvm_code_shape (code:(tvm_inst)list) : bool =
       (!i. 0i <= i ==> i < ilength code ==>
          tvm_inst_shape (inth i code))`);
PROOF thm tvm_targets_valid_def = new_fun_definition(
    `tvm_targets_valid (code:(tvm_inst)list) : bool =
       (!i. 0i <= i ==> i < ilength code ==>
          (tvm_opcode_is_target (tvm_inst_op (inth i code)) ==>
           tvm_target_valid code (tvm_inst_imm (inth i code))))`);
PROOF thm tvm_load_ok_def = new_fun_definition(
    `tvm_load_ok (obj:tvm_object) : bool =
       (tvm_patches_valid (tvm_object_patches obj) &&
        tvm_code_shape (tvm_object_code obj))`);
PROOF thm tvm_object_wf_def = new_fun_definition(
    `tvm_object_wf (obj:tvm_object) : bool =
       (tvm_load_ok obj &&
        tvm_target_valid (tvm_object_code obj) (tvm_object_entry obj) &&
        tvm_targets_valid (tvm_object_code obj))`);

PROOF int _e_tvm_target_valid =
    cst_add_const_to_header(`tvm_target_valid`);
PROOF int _e_tvm_opcode_has_imm =
    cst_add_const_to_header(`tvm_opcode_has_imm`);
PROOF int _e_tvm_opcode_is_target =
    cst_add_const_to_header(`tvm_opcode_is_target`);
PROOF int _e_tvm_inst_shape =
    cst_add_const_to_header(`tvm_inst_shape`);
PROOF int _e_tvm_patch_valid =
    cst_add_const_to_header(`tvm_patch_valid`);
PROOF int _e_tvm_patches_valid =
    cst_add_const_to_header(`tvm_patches_valid`);
PROOF int _e_tvm_code_shape =
    cst_add_const_to_header(`tvm_code_shape`);
PROOF int _e_tvm_targets_valid =
    cst_add_const_to_header(`tvm_targets_valid`);
PROOF int _e_tvm_load_ok = cst_add_const_to_header(`tvm_load_ok`);
PROOF int _e_tvm_object_wf =
    cst_add_const_to_header(`tvm_object_wf`);

PROOF thm tvm_apply_patches_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tvm_apply_patches ([]:(tvm_patch)list) (mem:int->int) = mem) &&
     (!patch rest mem.
       tvm_apply_patches ((patch:tvm_patch) :: rest) (mem:int->int) =
         tvm_apply_patches rest
           (tower_setb mem (tvm_patch_addr patch)
              (tvm_patch_byte patch)))`);
PROOF thm tvm_initial_state_def = new_fun_definition(
    `tvm_initial_state (obj:tvm_object) (input:(int)list) : tvm_state =
       TVMState (tvm_object_entry obj) [] []
         (tvm_apply_patches (tvm_object_patches obj) tower_zero_mem)
         input []`);
PROOF thm tvm_unloaded_state_def = new_fun_definition(
    `tvm_unloaded_state (obj:tvm_object) (input:(int)list) : tvm_state =
       TVMState (tvm_object_entry obj) [] [] tower_zero_mem input []`);
PROOF thm tvm_valid_input_def = new_fun_definition(
    `tvm_valid_input (input:(int)list) : bool =
       ALL (\byte:int. tower_byte_value byte) input`);
PROOF thm tvm_decode_pair_valid_def = new_fun_definition(
    `tvm_decode_pair_valid (code:int) (imm:int) : bool =
       (0i <= code && code < 28i &&
        tvm_inst_shape (TVMInst (tvm_opcode_decode code) imm))`);
PROOF thm tvm_decode_pair_def = new_fun_definition(
    `tvm_decode_pair (code:int) (imm:int) : tvm_inst =
       TVMInst (tvm_opcode_decode code) imm`);

PROOF int _e_tvm_apply_patches =
    cst_add_const_to_header(`tvm_apply_patches`);
PROOF int _e_tvm_initial_state =
    cst_add_const_to_header(`tvm_initial_state`);
PROOF int _e_tvm_unloaded_state =
    cst_add_const_to_header(`tvm_unloaded_state`);
PROOF int _e_tvm_valid_input =
    cst_add_const_to_header(`tvm_valid_input`);
PROOF int _e_tvm_decode_pair_valid =
    cst_add_const_to_header(`tvm_decode_pair_valid`);
PROOF int _e_tvm_decode_pair =
    cst_add_const_to_header(`tvm_decode_pair`);

/* State reconstruction helpers.  Every error branch returns the original
 * state, so failed checks cannot consume stacks or change observable I/O. */
PROOF thm tvm_next_state_def = new_fun_definition(
    `tvm_next_state (st:tvm_state) (stack:(int)list)
       (calls:(int)list) (mem:int->int) (input:(int)list)
       (output:(int)list) : tvm_state =
       TVMState (tvm_pc st + 1i) stack calls mem input output`);
PROOF thm tvm_jump_state_def = new_fun_definition(
    `tvm_jump_state (st:tvm_state) (target:int) (stack:(int)list)
       (calls:(int)list) (mem:int->int) (input:(int)list)
       (output:(int)list) : tvm_state =
       TVMState target stack calls mem input output`);
PROOF int _e_tvm_next_state =
    cst_add_const_to_header(`tvm_next_state`);
PROOF int _e_tvm_jump_state =
    cst_add_const_to_header(`tvm_jump_state`);

/* One selector-form equation per opcode. */
PROOF thm tvm_inst_step_def = new_rec_definition(
    tvm_opcode_RECURSION,
    `(!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMPushOp (imm:int)
         (st:tvm_state) =
       (if ilength (tvm_stack st) < 65536i
        then TVMStepState
          (tvm_next_state st
            ((tower_wrap64 imm) :: tvm_stack st)
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMPopOp (imm:int)
         (st:tvm_state) =
       (if 1i <= ilength (tvm_stack st)
        then TVMStepState
          (tvm_next_state st (TL (tvm_stack st))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMDupOp (imm:int)
         (st:tvm_state) =
       (if 1i <= ilength (tvm_stack st) &&
           ilength (tvm_stack st) < 65536i
        then TVMStepState
          (tvm_next_state st
            (HD (tvm_stack st) :: tvm_stack st)
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMSwapOp (imm:int)
         (st:tvm_state) =
       (if 2i <= ilength (tvm_stack st)
        then TVMStepState
          (tvm_next_state st
            (HD (TL (tvm_stack st)) :: HD (tvm_stack st) ::
              TL (TL (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMLoadOp (imm:int)
         (st:tvm_state) =
       (if 1i <= ilength (tvm_stack st) &&
           tower_word_valid (HD (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_getw (tvm_mem st) (HD (tvm_stack st)) ::
              TL (tvm_stack st))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMStoreOp (imm:int)
         (st:tvm_state) =
       (if 2i <= ilength (tvm_stack st) &&
           tower_word_valid (HD (tvm_stack st))
        then TVMStepState
          (tvm_next_state st (TL (TL (tvm_stack st)))
            (tvm_calls st)
            (tower_setw (tvm_mem st) (HD (tvm_stack st))
              (HD (TL (tvm_stack st))))
            (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMLoadBOp (imm:int)
         (st:tvm_state) =
       (if 1i <= ilength (tvm_stack st) &&
           tower_addr_valid (HD (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_getb (tvm_mem st) (HD (tvm_stack st)) ::
              TL (tvm_stack st))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMStoreBOp (imm:int)
         (st:tvm_state) =
       (if 2i <= ilength (tvm_stack st) &&
           tower_addr_valid (HD (tvm_stack st))
        then TVMStepState
          (tvm_next_state st (TL (TL (tvm_stack st)))
            (tvm_calls st)
            (tower_setb (tvm_mem st) (HD (tvm_stack st))
              (HD (TL (tvm_stack st))))
            (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMAddOp (imm:int)
         (st:tvm_state) =
       (if 2i <= ilength (tvm_stack st)
        then TVMStepState
          (tvm_next_state st
            (tower_add (HD (TL (tvm_stack st))) (HD (tvm_stack st)) ::
              TL (TL (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMSubOp (imm:int)
         (st:tvm_state) =
       (if 2i <= ilength (tvm_stack st)
        then TVMStepState
          (tvm_next_state st
            (tower_sub (HD (TL (tvm_stack st))) (HD (tvm_stack st)) ::
              TL (TL (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMMulOp (imm:int)
         (st:tvm_state) =
       (if 2i <= ilength (tvm_stack st)
        then TVMStepState
          (tvm_next_state st
            (tower_mul (HD (TL (tvm_stack st))) (HD (tvm_stack st)) ::
              TL (TL (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMDivOp (imm:int)
         (st:tvm_state) =
       (if 2i <= ilength (tvm_stack st) &&
           ~(HD (tvm_stack st) == 0i)
        then TVMStepState
          (tvm_next_state st
            (tower_div (HD (TL (tvm_stack st))) (HD (tvm_stack st)) ::
              TL (TL (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMModOp (imm:int)
         (st:tvm_state) =
       (if 2i <= ilength (tvm_stack st) &&
           ~(HD (tvm_stack st) == 0i)
        then TVMStepState
          (tvm_next_state st
            (tower_mod (HD (TL (tvm_stack st))) (HD (tvm_stack st)) ::
              TL (TL (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMEqOp (imm:int)
         (st:tvm_state) =
       (if 2i <= ilength (tvm_stack st)
        then TVMStepState
          (tvm_next_state st
            (tower_bool
              (HD (TL (tvm_stack st)) == HD (tvm_stack st)) ::
              TL (TL (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMNeOp (imm:int)
         (st:tvm_state) =
       (if 2i <= ilength (tvm_stack st)
        then TVMStepState
          (tvm_next_state st
            (tower_bool
              (~(HD (TL (tvm_stack st)) == HD (tvm_stack st))) ::
              TL (TL (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMLtOp (imm:int)
         (st:tvm_state) =
       (if 2i <= ilength (tvm_stack st)
        then TVMStepState
          (tvm_next_state st
            (tower_bool
              (HD (TL (tvm_stack st)) < HD (tvm_stack st)) ::
              TL (TL (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMLeOp (imm:int)
         (st:tvm_state) =
       (if 2i <= ilength (tvm_stack st)
        then TVMStepState
          (tvm_next_state st
            (tower_bool
              (HD (TL (tvm_stack st)) <= HD (tvm_stack st)) ::
              TL (TL (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMGtOp (imm:int)
         (st:tvm_state) =
       (if 2i <= ilength (tvm_stack st)
        then TVMStepState
          (tvm_next_state st
            (tower_bool
              (HD (tvm_stack st) < HD (TL (tvm_stack st))) ::
              TL (TL (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMGeOp (imm:int)
         (st:tvm_state) =
       (if 2i <= ilength (tvm_stack st)
        then TVMStepState
          (tvm_next_state st
            (tower_bool
              (HD (tvm_stack st) <= HD (TL (tvm_stack st))) ::
              TL (TL (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMJmpOp (imm:int)
         (st:tvm_state) =
       (if tvm_target_valid code imm
        then TVMStepState
          (tvm_jump_state st imm (tvm_stack st) (tvm_calls st)
            (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMJzOp (imm:int)
         (st:tvm_state) =
       (if 1i <= ilength (tvm_stack st)
        then if HD (tvm_stack st) == 0i
             then if tvm_target_valid code imm
                  then TVMStepState
                    (tvm_jump_state st imm (TL (tvm_stack st))
                      (tvm_calls st) (tvm_mem st) (tvm_input st)
                      (tvm_output st))
                  else TVMStepError st
             else TVMStepState
               (tvm_next_state st (TL (tvm_stack st))
                 (tvm_calls st) (tvm_mem st) (tvm_input st)
                 (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMJnzOp (imm:int)
         (st:tvm_state) =
       (if 1i <= ilength (tvm_stack st)
        then if ~(HD (tvm_stack st) == 0i)
             then if tvm_target_valid code imm
                  then TVMStepState
                    (tvm_jump_state st imm (TL (tvm_stack st))
                      (tvm_calls st) (tvm_mem st) (tvm_input st)
                      (tvm_output st))
                  else TVMStepError st
             else TVMStepState
               (tvm_next_state st (TL (tvm_stack st))
                 (tvm_calls st) (tvm_mem st) (tvm_input st)
                 (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMCallOp (imm:int)
         (st:tvm_state) =
       (if tvm_target_valid code imm &&
           ilength (tvm_calls st) < 65536i
        then TVMStepState
          (tvm_jump_state st imm (tvm_stack st)
            ((tvm_pc st + 1i) :: tvm_calls st)
            (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMRetOp (imm:int)
         (st:tvm_state) =
       (if 1i <= ilength (tvm_calls st)
        then TVMStepState
          (tvm_jump_state st (HD (tvm_calls st)) (tvm_stack st)
            (TL (tvm_calls st)) (tvm_mem st) (tvm_input st)
            (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMGetcOp (imm:int)
         (st:tvm_state) =
       (if ilength (tvm_stack st) < 65536i
        then if tvm_input st == []
             then TVMStepState
               (tvm_next_state st ((--1i) :: tvm_stack st)
                 (tvm_calls st) (tvm_mem st) (tvm_input st)
                 (tvm_output st))
             else TVMStepState
               (tvm_next_state st
                 (tower_u8 (HD (tvm_input st)) :: tvm_stack st)
                 (tvm_calls st) (tvm_mem st) (TL (tvm_input st))
                 (tvm_output st))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMPutcOp (imm:int)
         (st:tvm_state) =
       (if 1i <= ilength (tvm_stack st)
        then TVMStepState
          (tvm_next_state st (TL (tvm_stack st))
            (tvm_calls st) (tvm_mem st) (tvm_input st)
            (tvm_output st ++ [tower_u8 (HD (tvm_stack st))]))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMPutiOp (imm:int)
         (st:tvm_state) =
       (if 1i <= ilength (tvm_stack st)
        then TVMStepState
          (tvm_next_state st (TL (tvm_stack st))
            (tvm_calls st) (tvm_mem st) (tvm_input st)
            (tvm_output st ++ tower_decimal (HD (tvm_stack st))))
        else TVMStepError st)) &&
     (!code imm st.
       tvm_inst_step (code:(tvm_inst)list) TVMHaltOp (imm:int)
         (st:tvm_state) =
       (if 1i <= ilength (tvm_stack st) &&
           tower_byte_value (HD (tvm_stack st))
        then TVMStepHalt
          (TVMState (tvm_pc st) (TL (tvm_stack st)) (tvm_calls st)
            (tvm_mem st) (tvm_input st) (tvm_output st))
          (HD (tvm_stack st))
        else TVMStepError st))`);
PROOF int _e_tvm_inst_step =
    cst_add_const_to_header(`tvm_inst_step`);

PROOF static thm tvm_transition_clause(size_t index) {
  thm clause = tvm_inst_step_def;
  for (size_t i = 0; i < index; ++i) {
    clause = conjunct2_rule(clause);
  }
  return index == 27 ? clause : conjunct1_rule(clause);
}
PROOF thm tvm_push_transition = tvm_transition_clause(0);
PROOF thm tvm_pop_transition = tvm_transition_clause(1);
PROOF thm tvm_dup_transition = tvm_transition_clause(2);
PROOF thm tvm_swap_transition = tvm_transition_clause(3);
PROOF thm tvm_load_transition = tvm_transition_clause(4);
PROOF thm tvm_store_transition = tvm_transition_clause(5);
PROOF thm tvm_loadb_transition = tvm_transition_clause(6);
PROOF thm tvm_storeb_transition = tvm_transition_clause(7);
PROOF thm tvm_add_transition = tvm_transition_clause(8);
PROOF thm tvm_sub_transition = tvm_transition_clause(9);
PROOF thm tvm_mul_transition = tvm_transition_clause(10);
PROOF thm tvm_div_transition = tvm_transition_clause(11);
PROOF thm tvm_mod_transition = tvm_transition_clause(12);
PROOF thm tvm_eq_transition = tvm_transition_clause(13);
PROOF thm tvm_ne_transition = tvm_transition_clause(14);
PROOF thm tvm_lt_transition = tvm_transition_clause(15);
PROOF thm tvm_le_transition = tvm_transition_clause(16);
PROOF thm tvm_gt_transition = tvm_transition_clause(17);
PROOF thm tvm_ge_transition = tvm_transition_clause(18);
PROOF thm tvm_jmp_transition = tvm_transition_clause(19);
PROOF thm tvm_jz_transition = tvm_transition_clause(20);
PROOF thm tvm_jnz_transition = tvm_transition_clause(21);
PROOF thm tvm_call_transition = tvm_transition_clause(22);
PROOF thm tvm_ret_transition = tvm_transition_clause(23);
PROOF thm tvm_getc_transition = tvm_transition_clause(24);
PROOF thm tvm_putc_transition = tvm_transition_clause(25);
PROOF thm tvm_puti_transition = tvm_transition_clause(26);
PROOF thm tvm_halt_transition = tvm_transition_clause(27);

PROOF thm tvm_action_task_def = new_rec_definition(
    tvm_action_RECURSION,
    `(!obj st.
       tvm_action_task (obj:tvm_object) (TVMStepState (st:tvm_state)) =
         TVMRunTask obj st) &&
     (!obj st status.
       tvm_action_task (obj:tvm_object)
         (TVMStepHalt (st:tvm_state) (status:int)) =
         TVMDoneTask st status 0i) &&
     (!obj st.
       tvm_action_task (obj:tvm_object) (TVMStepError (st:tvm_state)) =
         TVMDoneTask st 2i 1i)`);
PROOF thm tvm_step_def = new_rec_definition(
    tvm_task_RECURSION,
    `(!obj input.
       tvm_step (TVMBoot (obj:tvm_object) (input:(int)list)) =
       (if tvm_load_ok obj
        then TVMRunTask obj (tvm_initial_state obj input)
        else TVMDoneTask (tvm_unloaded_state obj input) 3i 2i)) &&
     (!obj st.
       tvm_step (TVMRunTask (obj:tvm_object) (st:tvm_state)) =
       (if tvm_target_valid (tvm_object_code obj) (tvm_pc st)
        then tvm_action_task obj
          (tvm_inst_step (tvm_object_code obj)
            (tvm_inst_op
              (inth (tvm_pc st) (tvm_object_code obj)))
            (tvm_inst_imm
              (inth (tvm_pc st) (tvm_object_code obj))) st)
        else TVMDoneTask st 2i 1i)) &&
     (!st status kind.
       tvm_step
         (TVMDoneTask (st:tvm_state) (status:int) (kind:int)) =
         TVMDoneTask st status kind)`);
PROOF int _e_tvm_action_task =
    cst_add_const_to_header(`tvm_action_task`);
PROOF int _e_tvm_step = cst_add_const_to_header(`tvm_step`);

PROOF thm mk_tvm_step_deterministic(void) {
  gnode root = gnode_new_with_ccl(
      `!task next1 next2.
         tvm_step (task:tvm_task) == (next1:tvm_task) ==>
         tvm_step task == (next2:tvm_task) ==> next1 == next2`);
  gnode leaf = AUTO_INTROS_TAC(root);
  labeled_term_list as = goal_lasmps(leaf->g);
  thm h1 = assume_rule(as[0].tm);
  thm h2 = assume_rule(as[1].tm);
  ACCEPT_TAC(leaf, trans_rule(sym_rule(h1), h2));
  return gnode_prove(root);
}
PROOF thm tvm_step_deterministic = mk_tvm_step_deterministic();

PROOF thm mk_tvm_boot_valid(void) {
  gnode root = gnode_new_with_ccl(
      `!obj input. tvm_load_ok (obj:tvm_object) ==>
         tvm_step (TVMBoot obj (input:(int)list)) ==
           TVMRunTask obj (tvm_initial_state obj input)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm ok = assume_rule(goal_lasmps(leaf->g)[0].tm);
  CONV_TAC(leaf, rewrite_conv(THM_LIST(tvm_step_def, ok)));
  return gnode_prove(root);
}
PROOF thm tvm_boot_valid = mk_tvm_boot_valid();

PROOF thm mk_tvm_boot_malformed(void) {
  gnode root = gnode_new_with_ccl(
      `!obj input. ~(tvm_load_ok (obj:tvm_object)) ==>
         tvm_step (TVMBoot obj (input:(int)list)) ==
           TVMDoneTask (tvm_unloaded_state obj input) 3i 2i`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm bad = assume_rule(goal_lasmps(leaf->g)[0].tm);
  CONV_TAC(leaf, rewrite_conv(THM_LIST(tvm_step_def, bad)));
  return gnode_prove(root);
}
PROOF thm tvm_boot_malformed = mk_tvm_boot_malformed();

PROOF thm mk_tvm_pc_error(void) {
  gnode root = gnode_new_with_ccl(
      `!obj st.
         ~(tvm_target_valid (tvm_object_code (obj:tvm_object))
             (tvm_pc (st:tvm_state))) ==>
         tvm_step (TVMRunTask obj st) == TVMDoneTask st 2i 1i`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm bad = assume_rule(goal_lasmps(leaf->g)[0].tm);
  CONV_TAC(leaf, rewrite_conv(THM_LIST(tvm_step_def, bad)));
  return gnode_prove(root);
}
PROOF thm tvm_pc_error = mk_tvm_pc_error();

PROOF static conv tvm_reduce_rewrite(const thm_list ths) {
  return then_conv(rewrite_conv(ths),
                   get_conversion_by_name("INT_REDUCE_CONV"));
}

PROOF thm tvm_task_done_def = new_rec_definition(
    tvm_task_RECURSION,
    `(!obj input.
       tvm_task_done (TVMBoot (obj:tvm_object) (input:(int)list)) = F) &&
     (!obj st.
       tvm_task_done (TVMRunTask (obj:tvm_object) (st:tvm_state)) = F) &&
     (!st status kind.
       tvm_task_done
         (TVMDoneTask (st:tvm_state) (status:int) (kind:int)) = T)`);
PROOF thm tvm_task_outcome_def = new_rec_definition(
    tvm_task_RECURSION,
    `(!obj input.
       tvm_task_outcome
         (TVMBoot (obj:tvm_object) (input:(int)list)) =
         TVMOutcome (tvm_unloaded_state obj input) 3i 2i) &&
     (!obj st.
       tvm_task_outcome
         (TVMRunTask (obj:tvm_object) (st:tvm_state)) =
         TVMOutcome st 2i 1i) &&
     (!st status kind.
       tvm_task_outcome
         (TVMDoneTask (st:tvm_state) (status:int) (kind:int)) =
         TVMOutcome st status kind)`);
PROOF thm tvm_iter_def = new_rec_definition(
    get_theorem_by_name("num_RECURSION"),
    `(tvm_iter 0 (task:tvm_task) = task) &&
     (!n task.
       tvm_iter (SUC (n:num)) (task:tvm_task) =
         tvm_iter n (tvm_step task))`);
PROOF thm tvm_exec_def = new_fun_definition(
    `tvm_exec (task:tvm_task) (out:tvm_outcome) : bool =
       (?n st status kind.
          tvm_iter n task ==
            TVMDoneTask (st:tvm_state) (status:int) (kind:int) &&
          out == TVMOutcome st status kind)`);

PROOF int _e_tvm_task_done =
    cst_add_const_to_header(`tvm_task_done`);
PROOF int _e_tvm_task_outcome =
    cst_add_const_to_header(`tvm_task_outcome`);
PROOF int _e_tvm_iter = cst_add_const_to_header(`tvm_iter`);
PROOF int _e_tvm_exec = cst_add_const_to_header(`tvm_exec`);

PROOF thm mk_tvm_exec_done(void) {
  gnode root = gnode_new_with_ccl(
      `!st status kind.
         tvm_exec
           (TVMDoneTask (st:tvm_state) (status:int) (kind:int))
           (TVMOutcome st status kind)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode tgt = CONV_TAC(leaf, pure_rewrite_conv(THM_LIST(tvm_exec_def)));
  thm iter0 = inst_rule(TERM_PAIR_LIST(
      (term_pair){
        `TVMDoneTask (st:tvm_state) (status:int) (kind:int)`,
        `task:tvm_task`}), conjunct1_rule(tvm_iter_def));
  thm body = conj_rule(iter0,
      refl_rule(`TVMOutcome (st:tvm_state) (status:int) (kind:int)`));
  thm exs = exists_rule(
      `?n st0 status0 kind0.
         tvm_iter n
           (TVMDoneTask (st:tvm_state) (status:int) (kind:int)) ==
           TVMDoneTask (st0:tvm_state) (status0:int) (kind0:int) &&
         TVMOutcome st status kind == TVMOutcome st0 status0 kind0`,
      `0:num`, exists_rule(
        `?st0 status0 kind0.
           tvm_iter 0
             (TVMDoneTask (st:tvm_state) (status:int) (kind:int)) ==
             TVMDoneTask (st0:tvm_state) (status0:int) (kind0:int) &&
           TVMOutcome st status kind == TVMOutcome st0 status0 kind0`,
        `st:tvm_state`, exists_rule(
          `?status0 kind0.
             tvm_iter 0
               (TVMDoneTask (st:tvm_state) (status:int) (kind:int)) ==
               TVMDoneTask (st:tvm_state) (status0:int) (kind0:int) &&
             TVMOutcome st status kind == TVMOutcome st status0 kind0`,
          `status:int`, exists_rule(
            `?kind0.
               tvm_iter 0
                 (TVMDoneTask (st:tvm_state) (status:int) (kind:int)) ==
                 TVMDoneTask (st:tvm_state) (status:int) (kind0:int) &&
               TVMOutcome st status kind == TVMOutcome st status kind0`,
            `kind:int`, body))));
  ACCEPT_TAC(tgt, exs);
  return gnode_prove(root);
}
PROOF thm tvm_exec_done = mk_tvm_exec_done();

PROOF thm mk_tvm_exec_rule(void) {
  thm run = pure_rewrite_rule(THM_LIST(tvm_exec_def),
      assume_rule(
        `tvm_exec (tvm_step (task:tvm_task)) (out:tvm_outcome)`));
  thm body0 = assume_rule(
      `tvm_iter (n:num) (tvm_step (task:tvm_task)) ==
         TVMDoneTask (st0:tvm_state) (status0:int) (kind0:int) &&
       (out:tvm_outcome) == TVMOutcome st0 status0 kind0`);
  thm advanced = trans_rule(
      specl_rule(TERM_LIST(`n:num`, `task:tvm_task`),
        conjunct2_rule(tvm_iter_def)),
      conjunct1_rule(body0));
  thm body = conj_rule(advanced, conjunct2_rule(body0));
  thm exs = exists_rule(
      `?m st1 status1 kind1.
         tvm_iter m (task:tvm_task) ==
           TVMDoneTask (st1:tvm_state) (status1:int) (kind1:int) &&
         (out:tvm_outcome) == TVMOutcome st1 status1 kind1`,
      `SUC (n:num)`, exists_rule(
        `?st1 status1 kind1.
           tvm_iter (SUC (n:num)) (task:tvm_task) ==
             TVMDoneTask (st1:tvm_state) (status1:int) (kind1:int) &&
           (out:tvm_outcome) == TVMOutcome st1 status1 kind1`,
        `st0:tvm_state`, exists_rule(
          `?status1 kind1.
             tvm_iter (SUC (n:num)) (task:tvm_task) ==
               TVMDoneTask (st0:tvm_state) (status1:int) (kind1:int) &&
             (out:tvm_outcome) == TVMOutcome st0 status1 kind1`,
          `status0:int`, exists_rule(
            `?kind1.
               tvm_iter (SUC (n:num)) (task:tvm_task) ==
                 TVMDoneTask (st0:tvm_state) (status0:int) (kind1:int) &&
               (out:tvm_outcome) == TVMOutcome st0 status0 kind1`,
            `kind0:int`, body))));
  thm no_kind = choose_rule(`kind0:int`,
      assume_rule(
        `?kind0.
           tvm_iter (n:num) (tvm_step (task:tvm_task)) ==
             TVMDoneTask (st0:tvm_state) (status0:int) (kind0:int) &&
           (out:tvm_outcome) == TVMOutcome st0 status0 kind0`), exs);
  thm no_status = choose_rule(`status0:int`,
      assume_rule(
        `?status0 kind0.
           tvm_iter (n:num) (tvm_step (task:tvm_task)) ==
             TVMDoneTask (st0:tvm_state) (status0:int) (kind0:int) &&
           (out:tvm_outcome) == TVMOutcome st0 status0 kind0`), no_kind);
  thm no_state = choose_rule(`st0:tvm_state`,
      assume_rule(
        `?st0 status0 kind0.
           tvm_iter (n:num) (tvm_step (task:tvm_task)) ==
             TVMDoneTask (st0:tvm_state) (status0:int) (kind0:int) &&
           (out:tvm_outcome) == TVMOutcome st0 status0 kind0`), no_status);
  thm result = choose_rule(`n:num`, run, no_state);
  thm folded = eq_mp_rule(sym_rule(apply_conversion(
      pure_rewrite_conv(THM_LIST(tvm_exec_def)),
      `tvm_exec (task:tvm_task) (out:tvm_outcome)`)), result);
  return close_implication(
      `!task out.
         tvm_exec (tvm_step (task:tvm_task)) (out:tvm_outcome) ==>
         tvm_exec task out`, folded);
}
PROOF thm tvm_exec_rule = mk_tvm_exec_rule();

PROOF thm mk_tvm_done_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(task:tvm_task). tvm_task_done task ==>
         tvm_step task == task`);
  gnode_list cases = INDUCT_TAC(root, `task:tvm_task`);
  for (size_t i = 0; i < 2; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    thm impossible = conv_rule(tvm_reduce_rewrite(
        THM_LIST(tvm_task_done_def)),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    CONTR_TAC(leaf, impossible);
  }
  gnode done = AUTO_INTROS_TAC(cases[2]);
  CONV_TAC(done, tvm_reduce_rewrite(
      THM_LIST(tvm_task_done_def, tvm_step_def)));
  return gnode_prove(root);
}
PROOF thm tvm_done_step = mk_tvm_done_step();

PROOF thm mk_tvm_done_iter(void) {
  gnode root = gnode_new_with_ccl(
      `!(n:num) (task:tvm_task). tvm_task_done task ==>
         tvm_iter n task == task`);
  gnode_list cases = INDUCT_TAC(root, `n:num`);
  {
    gnode base = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(base, rewrite_conv(THM_LIST(tvm_iter_def)));
  }
  {
    gnode step = AUTO_INTROS_TAC(cases[1]);
    thm ih = mp_rule(spec_rule(`task:tvm_task`,
        assume_rule(goal_lasmps(step->g)[0].tm)),
        assume_rule(goal_lasmps(step->g)[1].tm));
    thm fixed = mp_rule(spec_rule(`task:tvm_task`, tvm_done_step),
        assume_rule(goal_lasmps(step->g)[1].tm));
    thm unfolded = specl_rule(TERM_LIST(`n:num`, `task:tvm_task`),
        conjunct2_rule(tvm_iter_def));
    thm congr = ap_term_rule(`tvm_iter (n:num)`, fixed);
    ACCEPT_TAC(step, trans_rule(unfolded, trans_rule(congr, ih)));
  }
  return gnode_prove(root);
}
PROOF thm tvm_done_iter = mk_tvm_done_iter();

PROOF thm mk_tvm_done_outcome_unique(void) {
  gnode root = gnode_new_with_ccl(
      `!(n:num). !(m:num) (task:tvm_task).
         tvm_task_done (tvm_iter n task) &&
         tvm_task_done (tvm_iter m task) ==>
         tvm_task_outcome (tvm_iter n task) ==
         tvm_task_outcome (tvm_iter m task)`);
  gnode_list ncases = INDUCT_TAC(root, `n:num`);
  {
    gnode base = AUTO_INTROS_TAC(ncases[0]);
    thm both = assume_rule(goal_lasmps(base->g)[0].tm);
    thm done = conv_rule(rewrite_conv(THM_LIST(tvm_iter_def)),
        conjunct1_rule(both));
    thm fixed = mp_rule(specl_rule(TERM_LIST(`m:num`, `task:tvm_task`),
        tvm_done_iter), done);
    thm left = ap_term_rule(`tvm_task_outcome`,
        inst_rule(TERM_PAIR_LIST(
          (term_pair){`task:tvm_task`, `task:tvm_task`}),
          conjunct1_rule(tvm_iter_def)));
    thm right = ap_term_rule(`tvm_task_outcome`, fixed);
    ACCEPT_TAC(base, trans_rule(left, sym_rule(right)));
  }
  gnode_list mcases = INDUCT_TAC(ncases[1], `m:num`);
  {
    gnode base = AUTO_INTROS_TAC(mcases[0]);
    thm both = assume_rule(goal_lasmps(base->g)[1].tm);
    thm done = conv_rule(rewrite_conv(THM_LIST(tvm_iter_def)),
        conjunct2_rule(both));
    thm fixed = mp_rule(specl_rule(
        TERM_LIST(`SUC (n:num)`, `task:tvm_task`),
        tvm_done_iter), done);
    thm left = ap_term_rule(`tvm_task_outcome`, fixed);
    thm right = ap_term_rule(`tvm_task_outcome`,
        inst_rule(TERM_PAIR_LIST(
          (term_pair){`task:tvm_task`, `task:tvm_task`}),
          conjunct1_rule(tvm_iter_def)));
    ACCEPT_TAC(base, trans_rule(left, sym_rule(right)));
  }
  {
    gnode step = AUTO_INTROS_TAC(mcases[1]);
    thm both = assume_rule(goal_lasmps(step->g)[2].tm);
    thm left_done = conv_rule(rewrite_conv(THM_LIST(tvm_iter_def)),
        conjunct1_rule(both));
    thm right_done = conv_rule(rewrite_conv(THM_LIST(tvm_iter_def)),
        conjunct2_rule(both));
    thm ih = specl_rule(TERM_LIST(`n_:num`,
        `tvm_step (task:tvm_task)`),
        assume_rule(goal_lasmps(step->g)[0].tm));
    thm same = mp_rule(ih, conj_rule(left_done, right_done));
    gnode tgt = CONV_TAC(step, rewrite_conv(THM_LIST(tvm_iter_def)));
    ACCEPT_TAC(tgt, same);
  }
  return gnode_prove(root);
}
PROOF thm tvm_done_outcome_unique = mk_tvm_done_outcome_unique();

PROOF thm mk_tvm_exec_witness(void) {
  thm run = pure_rewrite_rule(THM_LIST(tvm_exec_def),
      assume_rule(`tvm_exec (task:tvm_task) (out:tvm_outcome)`));
  thm body0 = assume_rule(
      `tvm_iter (n:num) (task:tvm_task) ==
         TVMDoneTask (st:tvm_state) (status:int) (kind:int) &&
       (out:tvm_outcome) == TVMOutcome st status kind`);
  thm iter_eq = conjunct1_rule(body0);
  thm done = conv_rule(tvm_reduce_rewrite(
      THM_LIST(tvm_task_done_def)),
      ap_term_rule(`tvm_task_done`, iter_eq));
  thm iter_out = conv_rule(tvm_reduce_rewrite(
      THM_LIST(tvm_task_outcome_def)),
      ap_term_rule(`tvm_task_outcome`, iter_eq));
  thm out_eq = trans_rule(conjunct2_rule(body0), sym_rule(iter_out));
  thm exs = exists_rule(
      `?m. tvm_task_done (tvm_iter m (task:tvm_task)) &&
           (out:tvm_outcome) == tvm_task_outcome (tvm_iter m task)`,
      `n:num`, conj_rule(done, out_eq));
  thm no_kind = choose_rule(`kind:int`,
      assume_rule(
        `?kind.
           tvm_iter (n:num) (task:tvm_task) ==
             TVMDoneTask (st:tvm_state) (status:int) (kind:int) &&
           (out:tvm_outcome) == TVMOutcome st status kind`), exs);
  thm no_status = choose_rule(`status:int`,
      assume_rule(
        `?status kind.
           tvm_iter (n:num) (task:tvm_task) ==
             TVMDoneTask (st:tvm_state) (status:int) (kind:int) &&
           (out:tvm_outcome) == TVMOutcome st status kind`), no_kind);
  thm no_state = choose_rule(`st:tvm_state`,
      assume_rule(
        `?st status kind.
           tvm_iter (n:num) (task:tvm_task) ==
             TVMDoneTask (st:tvm_state) (status:int) (kind:int) &&
           (out:tvm_outcome) == TVMOutcome st status kind`), no_status);
  thm result = choose_rule(`n:num`, run, no_state);
  return close_implication(
      `!task out. tvm_exec (task:tvm_task) (out:tvm_outcome) ==>
         ?n. tvm_task_done (tvm_iter n task) &&
             out == tvm_task_outcome (tvm_iter n task)`, result);
}
PROOF thm tvm_exec_witness = mk_tvm_exec_witness();

PROOF thm mk_tvm_exec_deterministic(void) {
  thm h1 = assume_rule(
      `tvm_exec (task:tvm_task) (out1:tvm_outcome)`);
  thm h2 = assume_rule(
      `tvm_exec (task:tvm_task) (out2:tvm_outcome)`);
  thm ex1 = mp_rule(specl_rule(
      TERM_LIST(`task:tvm_task`, `out1:tvm_outcome`),
      tvm_exec_witness), h1);
  thm ex2 = mp_rule(specl_rule(
      TERM_LIST(`task:tvm_task`, `out2:tvm_outcome`),
      tvm_exec_witness), h2);
  thm b1 = assume_rule(
      `tvm_task_done (tvm_iter (n:num) (task:tvm_task)) &&
       (out1:tvm_outcome) == tvm_task_outcome (tvm_iter n task)`);
  thm b2 = assume_rule(
      `tvm_task_done (tvm_iter (m:num) (task:tvm_task)) &&
       (out2:tvm_outcome) == tvm_task_outcome (tvm_iter m task)`);
  thm same = mp_rule(specl_rule(
      TERM_LIST(`n:num`, `m:num`, `task:tvm_task`),
      tvm_done_outcome_unique),
      conj_rule(conjunct1_rule(b1), conjunct1_rule(b2)));
  thm result0 = trans_rule(conjunct2_rule(b1),
      trans_rule(same, sym_rule(conjunct2_rule(b2))));
  thm result1 = choose_rule(`m:num`, ex2, result0);
  thm result = choose_rule(`n:num`, ex1, result1);
  return close_implication(
      `!task out1 out2.
         tvm_exec (task:tvm_task) (out1:tvm_outcome) ==>
         tvm_exec task (out2:tvm_outcome) ==> out1 == out2`, result);
}
PROOF thm tvm_exec_deterministic = mk_tvm_exec_deterministic();

PROOF thm mk_tvm_exec_prefix(void) {
  gnode root = gnode_new_with_ccl(
      `!(n:num). !task out.
         tvm_exec (tvm_iter n (task:tvm_task)) (out:tvm_outcome) ==>
         tvm_exec task out`);
  gnode_list cases = INDUCT_TAC(root, `n:num`);
  {
    gnode base = AUTO_INTROS_TAC(cases[0]);
    thm run = conv_rule(rewrite_conv(THM_LIST(tvm_iter_def)),
        assume_rule(goal_lasmps(base->g)[0].tm));
    ACCEPT_TAC(base, run);
  }
  {
    gnode step = AUTO_INTROS_TAC(cases[1]);
    labeled_term_list as = goal_lasmps(step->g);
    thm run = conv_rule(rewrite_conv(THM_LIST(tvm_iter_def)),
        assume_rule(as[1].tm));
    thm tail = mp_rule(specl_rule(TERM_LIST(
        `tvm_step (task:tvm_task)`, `out:tvm_outcome`),
        assume_rule(as[0].tm)), run);
    thm result = mp_rule(specl_rule(TERM_LIST(
        `task:tvm_task`, `out:tvm_outcome`), tvm_exec_rule), tail);
    ACCEPT_TAC(step, result);
  }
  return gnode_prove(root);
}
PROOF thm tvm_exec_prefix = mk_tvm_exec_prefix();

PROOF thm mk_tvm_terminal_exec(void) {
  gnode root = gnode_new_with_ccl(
      `!(task:tvm_task). tvm_task_done task ==>
         tvm_exec task (tvm_task_outcome task)`);
  gnode_list cases = INDUCT_TAC(root, `task:tvm_task`);
  for (size_t i = 0; i < 2; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    thm impossible = conv_rule(tvm_reduce_rewrite(
        THM_LIST(tvm_task_done_def)),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    CONTR_TAC(leaf, impossible);
  }
  gnode done = AUTO_INTROS_TAC(cases[2]);
  CONV_TAC(done, tvm_reduce_rewrite(
      THM_LIST(tvm_task_done_def, tvm_task_outcome_def, tvm_exec_done)));
  return gnode_prove(root);
}
PROOF thm tvm_terminal_exec = mk_tvm_terminal_exec();

PROOF thm tvm_terminates_def = new_fun_definition(
    `tvm_terminates (obj:tvm_object) (input:(int)list)
       (output:(int)list) (status:int) : bool =
       (tvm_valid_input input && tower_byte_value status &&
        ?st.
          tvm_exec (TVMBoot obj input)
            (TVMOutcome (st:tvm_state) status 0i) &&
          tvm_output st == output)`);
PROOF thm tvm_errors_def = new_fun_definition(
    `tvm_errors (obj:tvm_object) (input:(int)list)
       (output:(int)list) : bool =
       (tvm_valid_input input &&
        ?st.
          tvm_exec (TVMBoot obj input)
            (TVMOutcome (st:tvm_state) 2i 1i) &&
          tvm_output st == output)`);
PROOF thm tvm_malformed_def = new_fun_definition(
    `tvm_malformed (obj:tvm_object) (input:(int)list) : bool =
       (?st.
          tvm_exec (TVMBoot obj input)
            (TVMOutcome (st:tvm_state) 3i 2i))`);
PROOF int _e_tvm_terminates =
    cst_add_const_to_header(`tvm_terminates`);
PROOF int _e_tvm_errors = cst_add_const_to_header(`tvm_errors`);
PROOF int _e_tvm_malformed =
    cst_add_const_to_header(`tvm_malformed`);

PROOF thm mk_tvm_load_rejects(void) {
  thm bad = assume_rule(`~(tvm_load_ok (obj:tvm_object))`);
  thm step_eq = mp_rule(specl_rule(TERM_LIST(
      `obj:tvm_object`, `input:(int)list`), tvm_boot_malformed), bad);
  thm done = specl_rule(TERM_LIST(
      `tvm_unloaded_state (obj:tvm_object) (input:(int)list)`,
      `3i:int`, `2i:int`), tvm_exec_done);
  thm lift = beta_norm(ap_term_rule(
      `\next:tvm_task.
         tvm_exec next
           (TVMOutcome
             (tvm_unloaded_state (obj:tvm_object) (input:(int)list))
             3i 2i)`, step_eq));
  thm after = eq_mp_rule(sym_rule(lift), done);
  thm result = mp_rule(specl_rule(TERM_LIST(
      `TVMBoot (obj:tvm_object) (input:(int)list)`,
      `TVMOutcome
        (tvm_unloaded_state (obj:tvm_object) (input:(int)list)) 3i 2i`),
      tvm_exec_rule), after);
  return close_implication(
      `!obj input. ~(tvm_load_ok (obj:tvm_object)) ==>
         tvm_exec (TVMBoot obj (input:(int)list))
           (TVMOutcome (tvm_unloaded_state obj input) 3i 2i)`, result);
}
PROOF thm tvm_load_rejects = mk_tvm_load_rejects();

PROOF thm mk_tvm_runtime_pc_error(void) {
  thm bad = assume_rule(
      `~(tvm_target_valid (tvm_object_code (obj:tvm_object))
           (tvm_pc (st:tvm_state)))`);
  thm step_eq = mp_rule(specl_rule(TERM_LIST(
      `obj:tvm_object`, `st:tvm_state`), tvm_pc_error), bad);
  thm done = specl_rule(TERM_LIST(
      `st:tvm_state`, `2i:int`, `1i:int`), tvm_exec_done);
  thm lift = beta_norm(ap_term_rule(
      `\next:tvm_task.
         tvm_exec next (TVMOutcome (st:tvm_state) 2i 1i)`, step_eq));
  thm after = eq_mp_rule(sym_rule(lift), done);
  thm result = mp_rule(specl_rule(TERM_LIST(
      `TVMRunTask (obj:tvm_object) (st:tvm_state)`,
      `TVMOutcome (st:tvm_state) 2i 1i`), tvm_exec_rule), after);
  return close_implication(
      `!obj st.
         ~(tvm_target_valid (tvm_object_code (obj:tvm_object))
             (tvm_pc (st:tvm_state))) ==>
         tvm_exec (TVMRunTask obj st) (TVMOutcome st 2i 1i)`, result);
}
PROOF thm tvm_runtime_pc_error = mk_tvm_runtime_pc_error();

PROOF thm mk_tvm_edge_semantics(void) {
  gnode root = gnode_new_with_ccl(
      `!pc calls mem input output.
       (tvm_inst_step ([]:(tvm_inst)list) TVMGetcOp 0i
          (TVMState (pc:int) [] (calls:(int)list) (mem:int->int)
            [] (output:(int)list)) ==
        TVMStepState
          (TVMState (pc + 1i) [--1i] calls mem [] output)) &&
       (tvm_inst_step ([]:(tvm_inst)list) TVMPutcOp 0i
          (TVMState pc [--1i] calls mem (input:(int)list) output) ==
        TVMStepState
          (TVMState (pc + 1i) [] calls mem input
            (output ++ [255i]))) &&
       (tvm_inst_step ([]:(tvm_inst)list) TVMDivOp 0i
          (TVMState pc
            [--1i; --9223372036854775808i]
            calls mem input output) ==
        TVMStepState
          (TVMState (pc + 1i) [--9223372036854775808i]
            calls mem input output)) &&
       (tvm_inst_step ([]:(tvm_inst)list) TVMModOp 0i
          (TVMState pc
            [--1i; --9223372036854775808i]
            calls mem input output) ==
        TVMStepState
          (TVMState (pc + 1i) [0i] calls mem input output)) &&
       (tvm_inst_step ([]:(tvm_inst)list) TVMJzOp 99i
          (TVMState pc [0i] calls mem input output) ==
        TVMStepError
          (TVMState pc [0i] calls mem input output)) &&
       (tvm_inst_step ([]:(tvm_inst)list) TVMJzOp 99i
          (TVMState pc [1i] calls mem input output) ==
        TVMStepState
          (TVMState (pc + 1i) [] calls mem input output))`);
  CONV_TAC(root, tvm_reduce_rewrite(THM_LIST(
      tvm_getc_transition, tvm_putc_transition,
      tvm_div_transition, tvm_mod_transition, tvm_jz_transition,
      tvm_pc_def, tvm_stack_def, tvm_calls_def, tvm_mem_def,
      tvm_input_def, tvm_output_def, tvm_next_state_def,
      tvm_target_valid_def, get_tower_u8_def(),
      get_tower_div_min_neg1(), get_tower_mod_min_neg1(),
      get_theorem_by_name("ILENGTH_DEF"),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"))));
  return gnode_prove(root);
}
PROOF thm tvm_edge_semantics = mk_tvm_edge_semantics();

PROOF thm mk_tvm_opcode_code_range(void) {
  gnode root = gnode_new_with_ccl(
      `!(op:tvm_opcode).
         0i <= tvm_opcode_code op && tvm_opcode_code op < 28i`);
  gnode_list cases = INDUCT_TAC(root, `op:tvm_opcode`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_TAC(cases[i], tvm_reduce_rewrite(THM_LIST(tvm_opcode_code_def)));
  }
  return gnode_prove(root);
}
PROOF thm tvm_opcode_code_range = mk_tvm_opcode_code_range();

PROOF static thm tvm_prove_inst_reconstruct(void) {
  gnode root = gnode_new_with_ccl(
      `!(inst:tvm_inst).
         TVMInst (tvm_inst_op inst) (tvm_inst_imm inst) == inst`);
  gnode_list cases = INDUCT_TAC(root, `inst:tvm_inst`);
  CONV_TAC(cases[0], reduce_rewrite_conv(THM_LIST(
      tvm_inst_op_def, tvm_inst_imm_def)));
  return gnode_prove(root);
}
PROOF thm tvm_inst_reconstruct = tvm_prove_inst_reconstruct();

PROOF thm mk_tvm_decode_encode_inst(void) {
  gnode root = gnode_new_with_ccl(
      `!(op:tvm_opcode). !imm.
         tvm_inst_shape (TVMInst op (imm:int)) ==>
         tvm_decode_pair_valid (tvm_opcode_code op) imm &&
         tvm_decode_pair (tvm_opcode_code op) imm == TVMInst op imm`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm shape = assume_rule(goal_lasmps(leaf->g)[0].tm);
  thm rng = spec_rule(`op:tvm_opcode`, tvm_opcode_code_range);
  thm round = spec_rule(`op:tvm_opcode`, tvm_opcode_roundtrip);
  thm inst_eq = beta_norm(ap_term_rule(
      `\decoded:tvm_opcode. TVMInst decoded (imm:int)`, round));
  thm shape_eq = beta_norm(ap_term_rule(
      `\inst:tvm_inst. tvm_inst_shape inst`, inst_eq));
  thm decoded_shape = eq_mp_rule(sym_rule(shape_eq), shape);
  thm valid_rhs = conj_rule(conjunct1_rule(rng),
      conj_rule(conjunct2_rule(rng), decoded_shape));
  thm valid_eq = inst_rule(TERM_PAIR_LIST(
      (term_pair){`tvm_opcode_code (op:tvm_opcode)`, `code:int`},
      (term_pair){`imm:int`, `imm:int`}), tvm_decode_pair_valid_def);
  thm valid = eq_mp_rule(sym_rule(valid_eq), valid_rhs);
  thm pair0 = inst_rule(TERM_PAIR_LIST(
      (term_pair){`tvm_opcode_code (op:tvm_opcode)`, `code:int`},
      (term_pair){`imm:int`, `imm:int`}), tvm_decode_pair_def);
  thm pair = trans_rule(pair0, inst_eq);
  ACCEPT_TAC(leaf, conj_rule(valid, pair));
  return gnode_prove(root);
}
PROOF thm tvm_decode_encode_inst = mk_tvm_decode_encode_inst();

PROOF thm mk_tvm_object_wf_load(void) {
  gnode root = gnode_new_with_ccl(
      `!obj. tvm_object_wf (obj:tvm_object) ==> tvm_load_ok obj`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = pure_rewrite_rule(THM_LIST(tvm_object_wf_def),
      assume_rule(goal_lasmps(leaf->g)[0].tm));
  ACCEPT_TAC(leaf, conjunct1_rule(wf));
  return gnode_prove(root);
}
PROOF thm tvm_object_wf_load = mk_tvm_object_wf_load();

PROOF thm get_tvm_opcode_recursion(void) { return tvm_opcode_RECURSION; }
PROOF thm get_tvm_inst_recursion(void) { return tvm_inst_RECURSION; }
PROOF thm get_tvm_patch_recursion(void) { return tvm_patch_RECURSION; }
PROOF thm get_tvm_object_recursion(void) { return tvm_object_RECURSION; }
PROOF thm get_tvm_state_recursion(void) { return tvm_state_RECURSION; }
PROOF thm get_tvm_task_recursion(void) { return tvm_task_RECURSION; }
PROOF thm get_tvm_outcome_recursion(void) { return tvm_outcome_RECURSION; }
PROOF thm get_tvm_opcode_code_def(void) { return tvm_opcode_code_def; }
PROOF thm get_tvm_opcode_decode_def(void) { return tvm_opcode_decode_def; }
PROOF thm get_tvm_opcode_roundtrip(void) { return tvm_opcode_roundtrip; }
PROOF thm get_tvm_opcode_code_range(void) {
  return tvm_opcode_code_range;
}
PROOF thm get_tvm_inst_op_def(void) { return tvm_inst_op_def; }
PROOF thm get_tvm_inst_imm_def(void) { return tvm_inst_imm_def; }
PROOF thm get_tvm_patch_addr_def(void) { return tvm_patch_addr_def; }
PROOF thm get_tvm_patch_byte_def(void) { return tvm_patch_byte_def; }
PROOF thm get_tvm_object_entry_def(void) { return tvm_object_entry_def; }
PROOF thm get_tvm_object_code_def(void) { return tvm_object_code_def; }
PROOF thm get_tvm_object_patches_def(void) {
  return tvm_object_patches_def;
}
PROOF thm get_tvm_state_selectors_def(void) {
  return conj_rule(tvm_pc_def,
      conj_rule(tvm_stack_def,
        conj_rule(tvm_calls_def,
          conj_rule(tvm_mem_def,
            conj_rule(tvm_input_def, tvm_output_def)))));
}
PROOF thm get_tvm_target_valid_def(void) { return tvm_target_valid_def; }
PROOF thm get_tvm_opcode_has_imm_def(void) {
  return tvm_opcode_has_imm_def;
}
PROOF thm get_tvm_opcode_is_target_def(void) {
  return tvm_opcode_is_target_def;
}
PROOF thm get_tvm_inst_shape_def(void) { return tvm_inst_shape_def; }
PROOF thm get_tvm_patch_valid_def(void) { return tvm_patch_valid_def; }
PROOF thm get_tvm_patches_valid_def(void) {
  return tvm_patches_valid_def;
}
PROOF thm get_tvm_code_shape_def(void) {
  return tvm_code_shape_def;
}
PROOF thm get_tvm_targets_valid_def(void) {
  return tvm_targets_valid_def;
}
PROOF thm get_tvm_load_ok_def(void) { return tvm_load_ok_def; }
PROOF thm get_tvm_object_wf_def(void) { return tvm_object_wf_def; }
PROOF thm get_tvm_apply_patches_def(void) {
  return tvm_apply_patches_def;
}
PROOF thm_list get_tvm_eval_defs(void) {
  return THM_LIST(
      tvm_inst_op_def, tvm_inst_imm_def,
      tvm_patch_addr_def, tvm_patch_byte_def,
      tvm_object_entry_def, tvm_object_code_def,
      tvm_object_patches_def, tvm_pc_def, tvm_stack_def,
      tvm_calls_def, tvm_mem_def, tvm_input_def, tvm_output_def,
      tvm_valid_input_def, tvm_target_valid_def, tvm_apply_patches_def,
      tvm_initial_state_def, tvm_unloaded_state_def,
      tvm_next_state_def, tvm_jump_state_def,
      tvm_inst_step_def, tvm_action_task_def,
      tvm_step_def, tvm_iter_def, tvm_task_outcome_def,
      tvm_task_done_def, tvm_exec_def, tvm_terminates_def);
}

PROOF thm get_tvm_initial_state_def(void) { return tvm_initial_state_def; }
PROOF thm get_tvm_unloaded_state_def(void) {
  return tvm_unloaded_state_def;
}
PROOF thm get_tvm_next_state_def(void) { return tvm_next_state_def; }
PROOF thm get_tvm_jump_state_def(void) { return tvm_jump_state_def; }
PROOF thm get_tvm_decode_pair_valid_def(void) {
  return tvm_decode_pair_valid_def;
}
PROOF thm get_tvm_decode_pair_def(void) { return tvm_decode_pair_def; }
PROOF thm get_tvm_decode_encode_inst(void) {
  return tvm_decode_encode_inst;
}
PROOF thm get_tvm_inst_reconstruct(void) {
  return tvm_inst_reconstruct;
}
PROOF thm get_tvm_object_wf_load(void) { return tvm_object_wf_load; }
PROOF thm get_tvm_inst_step_def(void) { return tvm_inst_step_def; }
PROOF thm get_tvm_push_transition(void) { return tvm_push_transition; }
PROOF thm get_tvm_pop_transition(void) { return tvm_pop_transition; }
PROOF thm get_tvm_dup_transition(void) { return tvm_dup_transition; }
PROOF thm get_tvm_swap_transition(void) { return tvm_swap_transition; }
PROOF thm get_tvm_load_transition(void) { return tvm_load_transition; }
PROOF thm get_tvm_store_transition(void) { return tvm_store_transition; }
PROOF thm get_tvm_loadb_transition(void) { return tvm_loadb_transition; }
PROOF thm get_tvm_storeb_transition(void) { return tvm_storeb_transition; }
PROOF thm get_tvm_add_transition(void) { return tvm_add_transition; }
PROOF thm get_tvm_sub_transition(void) { return tvm_sub_transition; }
PROOF thm get_tvm_mul_transition(void) { return tvm_mul_transition; }
PROOF thm get_tvm_div_transition(void) { return tvm_div_transition; }
PROOF thm get_tvm_mod_transition(void) { return tvm_mod_transition; }
PROOF thm get_tvm_eq_transition(void) { return tvm_eq_transition; }
PROOF thm get_tvm_ne_transition(void) { return tvm_ne_transition; }
PROOF thm get_tvm_lt_transition(void) { return tvm_lt_transition; }
PROOF thm get_tvm_le_transition(void) { return tvm_le_transition; }
PROOF thm get_tvm_gt_transition(void) { return tvm_gt_transition; }
PROOF thm get_tvm_ge_transition(void) { return tvm_ge_transition; }
PROOF thm get_tvm_jmp_transition(void) { return tvm_jmp_transition; }
PROOF thm get_tvm_jz_transition(void) { return tvm_jz_transition; }
PROOF thm get_tvm_jnz_transition(void) { return tvm_jnz_transition; }
PROOF thm get_tvm_call_transition(void) { return tvm_call_transition; }
PROOF thm get_tvm_ret_transition(void) { return tvm_ret_transition; }
PROOF thm get_tvm_getc_transition(void) { return tvm_getc_transition; }
PROOF thm get_tvm_putc_transition(void) { return tvm_putc_transition; }
PROOF thm get_tvm_puti_transition(void) { return tvm_puti_transition; }
PROOF thm get_tvm_halt_transition(void) { return tvm_halt_transition; }
PROOF thm get_tvm_step_def(void) { return tvm_step_def; }
PROOF thm get_tvm_action_task_def(void) { return tvm_action_task_def; }
PROOF thm get_tvm_iter_def(void) { return tvm_iter_def; }
PROOF thm get_tvm_step_deterministic(void) {
  return tvm_step_deterministic;
}
PROOF thm get_tvm_exec_def(void) { return tvm_exec_def; }
PROOF thm get_tvm_exec_done(void) { return tvm_exec_done; }
PROOF thm get_tvm_exec_rule(void) { return tvm_exec_rule; }
PROOF thm get_tvm_exec_prefix(void) { return tvm_exec_prefix; }
PROOF thm get_tvm_deterministic(void) {
  return tvm_exec_deterministic;
}
PROOF thm get_tvm_terminates_def(void) { return tvm_terminates_def; }
PROOF thm get_tvm_errors_def(void) { return tvm_errors_def; }
PROOF thm get_tvm_malformed_def(void) { return tvm_malformed_def; }
PROOF thm get_tvm_load_rejects(void) { return tvm_load_rejects; }
PROOF thm get_tvm_runtime_pc_error(void) { return tvm_runtime_pc_error; }
PROOF thm get_tvm_edge_semantics(void) { return tvm_edge_semantics; }

PROOF static int _tvm_model_audit(void) {
  thm_list pubs = THM_LIST(
      tvm_opcode_RECURSION, tvm_inst_RECURSION, tvm_patch_RECURSION,
      tvm_object_RECURSION, tvm_state_RECURSION, tvm_task_RECURSION,
      tvm_outcome_RECURSION, tvm_opcode_code_def, tvm_opcode_decode_def,
      tvm_opcode_roundtrip, tvm_opcode_code_range,
      tvm_inst_op_def, tvm_inst_imm_def, tvm_patch_addr_def,
      tvm_patch_byte_def, tvm_object_entry_def, tvm_object_code_def,
      tvm_object_patches_def, tvm_pc_def, tvm_stack_def, tvm_calls_def,
      tvm_mem_def, tvm_input_def, tvm_output_def, tvm_target_valid_def,
      tvm_opcode_has_imm_def, tvm_opcode_is_target_def,
      tvm_inst_shape_def, tvm_patch_valid_def, tvm_load_ok_def,
      tvm_object_wf_def, tvm_apply_patches_def, tvm_initial_state_def,
      tvm_decode_pair_valid_def, tvm_decode_pair_def,
      tvm_inst_reconstruct, tvm_decode_encode_inst,
      tvm_object_wf_load, tvm_inst_step_def,
      tvm_push_transition, tvm_pop_transition, tvm_dup_transition,
      tvm_swap_transition, tvm_load_transition, tvm_store_transition,
      tvm_loadb_transition, tvm_storeb_transition, tvm_add_transition,
      tvm_sub_transition, tvm_mul_transition, tvm_div_transition,
      tvm_mod_transition, tvm_eq_transition, tvm_ne_transition,
      tvm_lt_transition, tvm_le_transition, tvm_gt_transition,
      tvm_ge_transition, tvm_jmp_transition, tvm_jz_transition,
      tvm_jnz_transition, tvm_call_transition, tvm_ret_transition,
      tvm_getc_transition, tvm_putc_transition, tvm_puti_transition,
      tvm_halt_transition, tvm_step_def, tvm_step_deterministic,
      tvm_exec_def, tvm_exec_done, tvm_exec_rule, tvm_exec_prefix,
      tvm_exec_deterministic, tvm_terminates_def, tvm_errors_def,
      tvm_malformed_def, tvm_load_rejects, tvm_runtime_pc_error,
      tvm_edge_semantics);
  for (size_t i = 0; i < vector_size(pubs); ++i) {
    ENSURE_COND(!IS_NULL(pubs[i]), "TVM theorem %zu is empty", i);
    ENSURE_COND(vector_size(hyp(pubs[i])) == 0,
                "TVM theorem %zu has hypotheses", i);
  }
  thm_list transitions = THM_LIST(
      tvm_push_transition, tvm_pop_transition, tvm_dup_transition,
      tvm_swap_transition, tvm_load_transition, tvm_store_transition,
      tvm_loadb_transition, tvm_storeb_transition, tvm_add_transition,
      tvm_sub_transition, tvm_mul_transition, tvm_div_transition,
      tvm_mod_transition, tvm_eq_transition, tvm_ne_transition,
      tvm_lt_transition, tvm_le_transition, tvm_gt_transition,
      tvm_ge_transition, tvm_jmp_transition, tvm_jz_transition,
      tvm_jnz_transition, tvm_call_transition, tvm_ret_transition,
      tvm_getc_transition, tvm_putc_transition, tvm_puti_transition,
      tvm_halt_transition);
  ENSURE_COND(vector_size(transitions) == 28,
              "TVM does not expose exactly 28 transitions");
  for (size_t i = 0; i < 28; ++i) {
    ENSURE_COND(alpha_compare(concl(transitions[i]),
        concl(tvm_transition_clause(i))) == 0,
        "TVM transition %zu has the wrong equation", i);
  }
  ENSURE_COND(alpha_compare(concl(tvm_opcode_roundtrip),
      `!(op:tvm_opcode).
         tvm_opcode_decode (tvm_opcode_code op) == op`) == 0,
      "TVM opcode roundtrip has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tvm_opcode_code_range),
      `!(op:tvm_opcode).
         0i <= tvm_opcode_code op && tvm_opcode_code op < 28i`) == 0,
      "TVM opcode range has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tvm_inst_reconstruct),
      `!(inst:tvm_inst).
         TVMInst (tvm_inst_op inst) (tvm_inst_imm inst) == inst`) == 0,
      "TVM instruction reconstruction has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tvm_decode_encode_inst),
      `!(op:tvm_opcode). !imm.
         tvm_inst_shape (TVMInst op (imm:int)) ==>
         tvm_decode_pair_valid (tvm_opcode_code op) imm &&
         tvm_decode_pair (tvm_opcode_code op) imm == TVMInst op imm`) == 0,
      "TVM decoder bridge has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tvm_step_deterministic),
      `!task next1 next2.
         tvm_step (task:tvm_task) == (next1:tvm_task) ==>
         tvm_step task == (next2:tvm_task) ==> next1 == next2`) == 0,
      "TVM one-step determinism has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tvm_exec_rule),
      `!task out.
         tvm_exec (tvm_step (task:tvm_task)) (out:tvm_outcome) ==>
         tvm_exec task out`) == 0,
      "TVM one-step composition has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tvm_exec_prefix),
      `!(n:num). !task out.
         tvm_exec (tvm_iter n (task:tvm_task)) (out:tvm_outcome) ==>
         tvm_exec task out`) == 0,
      "TVM multistep composition has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tvm_exec_deterministic),
      `!task out1 out2.
         tvm_exec (task:tvm_task) (out1:tvm_outcome) ==>
         tvm_exec task (out2:tvm_outcome) ==> out1 == out2`) == 0,
      "TVM terminal uniqueness has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tvm_load_rejects),
      `!obj input. ~(tvm_load_ok (obj:tvm_object)) ==>
         tvm_exec (TVMBoot obj (input:(int)list))
           (TVMOutcome (tvm_unloaded_state obj input) 3i 2i)`) == 0,
      "TVM malformed-loader theorem has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tvm_terminates_def),
      `tvm_terminates (obj:tvm_object) (input:(int)list)
         (output:(int)list) (status:int) <=>
       (tvm_valid_input input && tower_byte_value status &&
        ?st.
          tvm_exec (TVMBoot obj input)
            (TVMOutcome (st:tvm_state) status 0i) &&
          tvm_output st == output)`) == 0,
      "TVM termination definition has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(get_tvm_edge_semantics()),
      `!pc calls mem input output.
       (tvm_inst_step ([]:(tvm_inst)list) TVMGetcOp 0i
          (TVMState (pc:int) [] (calls:(int)list) (mem:int->int)
            [] (output:(int)list)) ==
        TVMStepState
          (TVMState (pc + 1i) [--1i] calls mem [] output)) &&
       (tvm_inst_step ([]:(tvm_inst)list) TVMPutcOp 0i
          (TVMState pc [--1i] calls mem (input:(int)list) output) ==
        TVMStepState
          (TVMState (pc + 1i) [] calls mem input
            (output ++ [255i]))) &&
       (tvm_inst_step ([]:(tvm_inst)list) TVMDivOp 0i
          (TVMState pc
            [--1i; --9223372036854775808i]
            calls mem input output) ==
        TVMStepState
          (TVMState (pc + 1i) [--9223372036854775808i]
            calls mem input output)) &&
       (tvm_inst_step ([]:(tvm_inst)list) TVMModOp 0i
          (TVMState pc
            [--1i; --9223372036854775808i]
            calls mem input output) ==
        TVMStepState
          (TVMState (pc + 1i) [0i] calls mem input output)) &&
       (tvm_inst_step ([]:(tvm_inst)list) TVMJzOp 99i
          (TVMState pc [0i] calls mem input output) ==
        TVMStepError
          (TVMState pc [0i] calls mem input output)) &&
       (tvm_inst_step ([]:(tvm_inst)list) TVMJzOp 99i
          (TVMState pc [1i] calls mem input output) ==
        TVMStepState
          (TVMState (pc + 1i) [] calls mem input output))`) == 0,
      "TVM edge-semantics theorem has the wrong conclusion");
  ENSURE_COND(vector_size(get_all_axioms()) == _tvm_axioms_before,
              "TVM model introduced an axiom");
  return 0;
err:
  ERR_FUN_PUTS("_tvm_model_audit");
  return -1;
}
PROOF int _tvm_model_audit_run = _tvm_model_audit();
