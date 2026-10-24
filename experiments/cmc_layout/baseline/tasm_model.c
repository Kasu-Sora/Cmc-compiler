#include "proof/proof.h"
#include "userlib/renderers.h"
#include "tvm_model.h"
#require "tvm_model.c"
#include "tasm_model.h"
#include "userlib/proof.h"

PROOF static size_t _tasm_axioms_before = vector_size(get_all_axioms());

PROOF indtype tasm_section_ty = new_datatype_definition(
    "tasm_section = TasmCode | TasmData");
PROOF indtype tasm_operand_ty = new_datatype_definition(
    "tasm_operand = TasmNoOperand | TasmImm int"
    " | TasmCodeRef int | TasmDataRef int");
PROOF indtype tasm_item_ty = new_datatype_definition(
    "tasm_item = TasmSection int tasm_section"
    " | TasmEntry int int | TasmLabel int int"
    " | TasmInstr int tvm_opcode tasm_operand"
    " | TasmWord int (int)list | TasmByte int (int)list"
    " | TasmAsciz int (int)list | TasmSpace int int");
PROOF indtype tasm_binding_ty = new_datatype_definition(
    "tasm_binding = TasmBinding int tasm_section int");
PROOF indtype tasm_error_ty = new_datatype_definition(
    "tasm_error = TasmError int int");
PROOF indtype tasm_result_ty = new_datatype_definition(
    "tasm_result = TasmOk tvm_object | TasmFail int int");

PROOF thm tasm_section_RECURSION = tasm_section_ty.rec;
PROOF thm tasm_operand_RECURSION = tasm_operand_ty.rec;
PROOF thm tasm_item_RECURSION = tasm_item_ty.rec;
PROOF thm tasm_binding_RECURSION = tasm_binding_ty.rec;
PROOF thm tasm_error_RECURSION = tasm_error_ty.rec;
PROOF thm tasm_result_RECURSION = tasm_result_ty.rec;

PROOF static int _t_tasm_section =
    cst_add_type_to_header("tasm_section", 0);
PROOF static int _t_tasm_operand =
    cst_add_type_to_header("tasm_operand", 0);
PROOF static int _t_tasm_item = cst_add_type_to_header("tasm_item", 0);
PROOF static int _t_tasm_binding =
    cst_add_type_to_header("tasm_binding", 0);
PROOF static int _t_tasm_error = cst_add_type_to_header("tasm_error", 0);
PROOF static int _t_tasm_result =
    cst_add_type_to_header("tasm_result", 0);

PROOF static int _c_TasmCode =
    cst_add_const_to_header(`TasmCode:tasm_section`);
PROOF static int _c_TasmData =
    cst_add_const_to_header(`TasmData:tasm_section`);
PROOF static int _c_TasmNoOperand =
    cst_add_const_to_header(`TasmNoOperand:tasm_operand`);
PROOF static int _c_TasmImm =
    cst_add_const_to_header(`TasmImm:int->tasm_operand`);
PROOF static int _c_TasmCodeRef =
    cst_add_const_to_header(`TasmCodeRef:int->tasm_operand`);
PROOF static int _c_TasmDataRef =
    cst_add_const_to_header(`TasmDataRef:int->tasm_operand`);
PROOF static int _c_TasmSection = cst_add_const_to_header(
    `TasmSection:int->tasm_section->tasm_item`);
PROOF static int _c_TasmEntry =
    cst_add_const_to_header(`TasmEntry:int->int->tasm_item`);
PROOF static int _c_TasmLabel =
    cst_add_const_to_header(`TasmLabel:int->int->tasm_item`);
PROOF static int _c_TasmInstr = cst_add_const_to_header(
    `TasmInstr:int->tvm_opcode->tasm_operand->tasm_item`);
PROOF static int _c_TasmWord =
    cst_add_const_to_header(`TasmWord:int->(int)list->tasm_item`);
PROOF static int _c_TasmByte =
    cst_add_const_to_header(`TasmByte:int->(int)list->tasm_item`);
PROOF static int _c_TasmAsciz =
    cst_add_const_to_header(`TasmAsciz:int->(int)list->tasm_item`);
PROOF static int _c_TasmSpace =
    cst_add_const_to_header(`TasmSpace:int->int->tasm_item`);
PROOF static int _c_TasmBinding = cst_add_const_to_header(
    `TasmBinding:int->tasm_section->int->tasm_binding`);
PROOF static int _c_TasmError =
    cst_add_const_to_header(`TasmError:int->int->tasm_error`);
PROOF static int _c_TasmOk =
    cst_add_const_to_header(`TasmOk:tvm_object->tasm_result`);
PROOF static int _c_TasmFail =
    cst_add_const_to_header(`TasmFail:int->int->tasm_result`);

PROOF thm tasm_item_line_def = new_rec_definition(
    tasm_item_RECURSION,
    `(!line sec. tasm_item_line
        (TasmSection (line:int) (sec:tasm_section)) = line) &&
     (!line label. tasm_item_line
        (TasmEntry (line:int) (label:int)) = line) &&
     (!line label. tasm_item_line
        (TasmLabel (line:int) (label:int)) = line) &&
     (!line op operand. tasm_item_line
        (TasmInstr (line:int) (op:tvm_opcode)
          (operand:tasm_operand)) = line) &&
     (!line values. tasm_item_line
        (TasmWord (line:int) (values:(int)list)) = line) &&
     (!line values. tasm_item_line
        (TasmByte (line:int) (values:(int)list)) = line) &&
     (!line bytes. tasm_item_line
        (TasmAsciz (line:int) (bytes:(int)list)) = line) &&
     (!line count. tasm_item_line
        (TasmSpace (line:int) (count:int)) = line)`);
PROOF thm tasm_item_kind_def = new_rec_definition(
    tasm_item_RECURSION,
    `(!line sec. tasm_item_kind
        (TasmSection (line:int) (sec:tasm_section)) = 0i) &&
     (!line label. tasm_item_kind
        (TasmEntry (line:int) (label:int)) = 1i) &&
     (!line label. tasm_item_kind
        (TasmLabel (line:int) (label:int)) = 2i) &&
     (!line op operand. tasm_item_kind
        (TasmInstr (line:int) (op:tvm_opcode)
          (operand:tasm_operand)) = 3i) &&
     (!line values. tasm_item_kind
        (TasmWord (line:int) (values:(int)list)) = 4i) &&
     (!line values. tasm_item_kind
        (TasmByte (line:int) (values:(int)list)) = 5i) &&
     (!line bytes. tasm_item_kind
        (TasmAsciz (line:int) (bytes:(int)list)) = 6i) &&
     (!line count. tasm_item_kind
        (TasmSpace (line:int) (count:int)) = 7i)`);
PROOF thm tasm_item_section_def = new_rec_definition(
    tasm_item_RECURSION,
    `(!line sec. tasm_item_section
        (TasmSection (line:int) (sec:tasm_section)) = sec) &&
     (!line label. tasm_item_section
        (TasmEntry (line:int) (label:int)) = TasmCode) &&
     (!line label. tasm_item_section
        (TasmLabel (line:int) (label:int)) = TasmCode) &&
     (!line op operand. tasm_item_section
        (TasmInstr (line:int) (op:tvm_opcode)
          (operand:tasm_operand)) = TasmCode) &&
     (!line values. tasm_item_section
        (TasmWord (line:int) (values:(int)list)) = TasmData) &&
     (!line values. tasm_item_section
        (TasmByte (line:int) (values:(int)list)) = TasmData) &&
     (!line bytes. tasm_item_section
        (TasmAsciz (line:int) (bytes:(int)list)) = TasmData) &&
     (!line count. tasm_item_section
        (TasmSpace (line:int) (count:int)) = TasmData)`);
PROOF thm tasm_item_label_def = new_rec_definition(
    tasm_item_RECURSION,
    `(!line sec. tasm_item_label
        (TasmSection (line:int) (sec:tasm_section)) = --1i) &&
     (!line label. tasm_item_label
        (TasmEntry (line:int) (label:int)) = label) &&
     (!line label. tasm_item_label
        (TasmLabel (line:int) (label:int)) = label) &&
     (!line op operand. tasm_item_label
        (TasmInstr (line:int) (op:tvm_opcode)
          (operand:tasm_operand)) = --1i) &&
     (!line values. tasm_item_label
        (TasmWord (line:int) (values:(int)list)) = --1i) &&
     (!line values. tasm_item_label
        (TasmByte (line:int) (values:(int)list)) = --1i) &&
     (!line bytes. tasm_item_label
        (TasmAsciz (line:int) (bytes:(int)list)) = --1i) &&
     (!line count. tasm_item_label
        (TasmSpace (line:int) (count:int)) = --1i)`);

PROOF thm tasm_item_opcode_def = new_rec_definition(
    tasm_item_RECURSION,
    `(!line sec. tasm_item_opcode
        (TasmSection (line:int) (sec:tasm_section)) = TVMHaltOp) &&
     (!line label. tasm_item_opcode
        (TasmEntry (line:int) (label:int)) = TVMHaltOp) &&
     (!line label. tasm_item_opcode
        (TasmLabel (line:int) (label:int)) = TVMHaltOp) &&
     (!line op operand. tasm_item_opcode
        (TasmInstr (line:int) (op:tvm_opcode)
          (operand:tasm_operand)) = op) &&
     (!line values. tasm_item_opcode
        (TasmWord (line:int) (values:(int)list)) = TVMHaltOp) &&
     (!line values. tasm_item_opcode
        (TasmByte (line:int) (values:(int)list)) = TVMHaltOp) &&
     (!line bytes. tasm_item_opcode
        (TasmAsciz (line:int) (bytes:(int)list)) = TVMHaltOp) &&
     (!line count. tasm_item_opcode
        (TasmSpace (line:int) (count:int)) = TVMHaltOp)`);
PROOF thm tasm_item_operand_def = new_rec_definition(
    tasm_item_RECURSION,
    `(!line sec. tasm_item_operand
        (TasmSection (line:int) (sec:tasm_section)) = TasmNoOperand) &&
     (!line label. tasm_item_operand
        (TasmEntry (line:int) (label:int)) = TasmNoOperand) &&
     (!line label. tasm_item_operand
        (TasmLabel (line:int) (label:int)) = TasmNoOperand) &&
     (!line op operand. tasm_item_operand
        (TasmInstr (line:int) (op:tvm_opcode)
          (operand:tasm_operand)) = operand) &&
     (!line values. tasm_item_operand
        (TasmWord (line:int) (values:(int)list)) = TasmNoOperand) &&
     (!line values. tasm_item_operand
        (TasmByte (line:int) (values:(int)list)) = TasmNoOperand) &&
     (!line bytes. tasm_item_operand
        (TasmAsciz (line:int) (bytes:(int)list)) = TasmNoOperand) &&
     (!line count. tasm_item_operand
        (TasmSpace (line:int) (count:int)) = TasmNoOperand)`);
PROOF thm tasm_item_values_def = new_rec_definition(
    tasm_item_RECURSION,
    `(!line sec. tasm_item_values
        (TasmSection (line:int) (sec:tasm_section)) = []) &&
     (!line label. tasm_item_values
        (TasmEntry (line:int) (label:int)) = []) &&
     (!line label. tasm_item_values
        (TasmLabel (line:int) (label:int)) = []) &&
     (!line op operand. tasm_item_values
        (TasmInstr (line:int) (op:tvm_opcode)
          (operand:tasm_operand)) = []) &&
     (!line values. tasm_item_values
        (TasmWord (line:int) (values:(int)list)) = values) &&
     (!line values. tasm_item_values
        (TasmByte (line:int) (values:(int)list)) = values) &&
     (!line bytes. tasm_item_values
        (TasmAsciz (line:int) (bytes:(int)list)) = bytes) &&
     (!line count. tasm_item_values
        (TasmSpace (line:int) (count:int)) = [])`);
PROOF thm tasm_item_count_def = new_rec_definition(
    tasm_item_RECURSION,
    `(!line sec. tasm_item_count
        (TasmSection (line:int) (sec:tasm_section)) = 0i) &&
     (!line label. tasm_item_count
        (TasmEntry (line:int) (label:int)) = 0i) &&
     (!line label. tasm_item_count
        (TasmLabel (line:int) (label:int)) = 0i) &&
     (!line op operand. tasm_item_count
        (TasmInstr (line:int) (op:tvm_opcode)
          (operand:tasm_operand)) = 0i) &&
     (!line values. tasm_item_count
        (TasmWord (line:int) (values:(int)list)) = 0i) &&
     (!line values. tasm_item_count
        (TasmByte (line:int) (values:(int)list)) = 0i) &&
     (!line bytes. tasm_item_count
        (TasmAsciz (line:int) (bytes:(int)list)) = 0i) &&
     (!line count. tasm_item_count
        (TasmSpace (line:int) (count:int)) = count)`);

PROOF int _e_tasm_item_line =
    cst_add_const_to_header(`tasm_item_line`);
PROOF int _e_tasm_item_kind =
    cst_add_const_to_header(`tasm_item_kind`);
PROOF int _e_tasm_item_section =
    cst_add_const_to_header(`tasm_item_section`);
PROOF int _e_tasm_item_label =
    cst_add_const_to_header(`tasm_item_label`);
PROOF int _e_tasm_item_opcode =
    cst_add_const_to_header(`tasm_item_opcode`);
PROOF int _e_tasm_item_operand =
    cst_add_const_to_header(`tasm_item_operand`);
PROOF int _e_tasm_item_values =
    cst_add_const_to_header(`tasm_item_values`);
PROOF int _e_tasm_item_count =
    cst_add_const_to_header(`tasm_item_count`);

PROOF thm tasm_operand_kind_def = new_rec_definition(
    tasm_operand_RECURSION,
    `(tasm_operand_kind TasmNoOperand = 0i) &&
     (!value. tasm_operand_kind (TasmImm (value:int)) = 1i) &&
     (!label. tasm_operand_kind (TasmCodeRef (label:int)) = 2i) &&
     (!label. tasm_operand_kind (TasmDataRef (label:int)) = 3i)`);
PROOF thm tasm_operand_value_def = new_rec_definition(
    tasm_operand_RECURSION,
    `(tasm_operand_value TasmNoOperand = 0i) &&
     (!value. tasm_operand_value (TasmImm (value:int)) = value) &&
     (!label. tasm_operand_value (TasmCodeRef (label:int)) = label) &&
     (!label. tasm_operand_value (TasmDataRef (label:int)) = label)`);
PROOF thm tasm_binding_id_def = new_rec_definition(
    tasm_binding_RECURSION,
    `tasm_binding_id
       (TasmBinding (label:int) (sec:tasm_section) (addr:int)) = label`);
PROOF thm tasm_binding_section_def = new_rec_definition(
    tasm_binding_RECURSION,
    `tasm_binding_section
       (TasmBinding (label:int) (sec:tasm_section) (addr:int)) = sec`);
PROOF thm tasm_binding_addr_def = new_rec_definition(
    tasm_binding_RECURSION,
    `tasm_binding_addr
       (TasmBinding (label:int) (sec:tasm_section) (addr:int)) = addr`);
PROOF thm tasm_error_line_def = new_rec_definition(
    tasm_error_RECURSION,
    `tasm_error_line (TasmError (line:int) (rank:int)) = line`);
PROOF thm tasm_error_rank_def = new_rec_definition(
    tasm_error_RECURSION,
    `tasm_error_rank (TasmError (line:int) (rank:int)) = rank`);

PROOF int _e_tasm_operand_kind =
    cst_add_const_to_header(`tasm_operand_kind`);
PROOF int _e_tasm_operand_value =
    cst_add_const_to_header(`tasm_operand_value`);
PROOF int _e_tasm_binding_id =
    cst_add_const_to_header(`tasm_binding_id`);
PROOF int _e_tasm_binding_section =
    cst_add_const_to_header(`tasm_binding_section`);
PROOF int _e_tasm_binding_addr =
    cst_add_const_to_header(`tasm_binding_addr`);
PROOF int _e_tasm_error_line =
    cst_add_const_to_header(`tasm_error_line`);
PROOF int _e_tasm_error_rank =
    cst_add_const_to_header(`tasm_error_rank`);

PROOF thm tasm_next_section_def = new_fun_definition(
    `tasm_next_section (sec:tasm_section) (item:tasm_item)
       : tasm_section =
       (if tasm_item_kind item == 0i
        then tasm_item_section item else sec)`);
PROOF thm tasm_code_delta_def = new_fun_definition(
    `tasm_code_delta (sec:tasm_section) (item:tasm_item) : int =
       (if sec == TasmCode && tasm_item_kind item == 3i then 1i else 0i)`);
PROOF thm tasm_data_delta_def = new_fun_definition(
    `tasm_data_delta (sec:tasm_section) (item:tasm_item) : int =
       (if sec == TasmData && tasm_item_kind item == 4i
        then 8i * ilength (tasm_item_values item)
        else if sec == TasmData && tasm_item_kind item == 5i
        then ilength (tasm_item_values item)
        else if sec == TasmData && tasm_item_kind item == 6i
        then ilength (tasm_item_values item) + 1i
        else if sec == TasmData && tasm_item_kind item == 7i
        then tasm_item_count item
        else 0i)`);
PROOF thm tasm_end_section_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_end_section (sec:tasm_section) ([]:(tasm_item)list) = sec) &&
     (!sec item rest.
       tasm_end_section (sec:tasm_section)
         ((item:tasm_item) :: rest) =
       tasm_end_section (tasm_next_section sec item) rest)`);
PROOF thm tasm_code_width_from_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_code_width_from (sec:tasm_section)
        ([]:(tasm_item)list) = 0i) &&
     (!sec item rest.
       tasm_code_width_from (sec:tasm_section)
         ((item:tasm_item) :: rest) =
       tasm_code_delta sec item +
       tasm_code_width_from (tasm_next_section sec item) rest)`);
PROOF thm tasm_data_width_from_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_data_width_from (sec:tasm_section)
        ([]:(tasm_item)list) = 0i) &&
     (!sec item rest.
       tasm_data_width_from (sec:tasm_section)
         ((item:tasm_item) :: rest) =
       tasm_data_delta sec item +
       tasm_data_width_from (tasm_next_section sec item) rest)`);
PROOF thm tasm_code_width_def = new_fun_definition(
    `tasm_code_width (items:(tasm_item)list) : int =
       tasm_code_width_from TasmCode items`);
PROOF thm tasm_data_width_def = new_fun_definition(
    `tasm_data_width (items:(tasm_item)list) : int =
       tasm_data_width_from TasmCode items`);

PROOF int _e_tasm_next_section =
    cst_add_const_to_header(`tasm_next_section`);
PROOF int _e_tasm_code_delta =
    cst_add_const_to_header(`tasm_code_delta`);
PROOF int _e_tasm_data_delta =
    cst_add_const_to_header(`tasm_data_delta`);
PROOF int _e_tasm_end_section =
    cst_add_const_to_header(`tasm_end_section`);
PROOF int _e_tasm_code_width =
    cst_add_const_to_header(`tasm_code_width`);
PROOF int _e_tasm_data_width =
    cst_add_const_to_header(`tasm_data_width`);

PROOF thm tasm_labels_from_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_labels_from (sec:tasm_section) (pc:int) (addr:int)
        ([]:(tasm_item)list) = []) &&
     (!sec pc addr item rest.
       tasm_labels_from (sec:tasm_section) (pc:int) (addr:int)
         ((item:tasm_item) :: rest) =
       ((if tasm_item_kind item == 2i
         then [TasmBinding (tasm_item_label item) sec
                 (if sec == TasmCode then pc else addr)]
         else []) ++
        tasm_labels_from (tasm_next_section sec item)
          (pc + tasm_code_delta sec item)
          (addr + tasm_data_delta sec item) rest))`);
PROOF thm tasm_labels_def = new_fun_definition(
    `tasm_labels (items:(tasm_item)list) : (tasm_binding)list =
       tasm_labels_from TasmCode 0i 8i items`);

PROOF thm tasm_binding_found_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_binding_found (label:int) ([]:(tasm_binding)list) = F) &&
     (!label binding rest.
       tasm_binding_found (label:int)
         ((binding:tasm_binding) :: rest) <=>
       (tasm_binding_id binding == label ||
        tasm_binding_found label rest))`);
PROOF thm tasm_binding_lookup_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_binding_lookup (label:int) ([]:(tasm_binding)list) =
        TasmBinding label TasmCode (--1i)) &&
     (!label binding rest.
       tasm_binding_lookup (label:int)
         ((binding:tasm_binding) :: rest) =
       (if tasm_binding_id binding == label
        then binding else tasm_binding_lookup label rest))`);
/*
 * The resolver owns a separate pass-one label environment.  Declarative
 * denotation continues to use tasm_labels, so resolver soundness must bridge
 * the two computations rather than succeeding by definitional identity.
 */
PROOF static thm tasm_resolver_labels_from_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_resolver_labels_from (sec:tasm_section) (pc:int) (addr:int)
        ([]:(tasm_item)list) = []) &&
     (!sec pc addr item rest.
       tasm_resolver_labels_from (sec:tasm_section) (pc:int) (addr:int)
         ((item:tasm_item) :: rest) =
       ((if tasm_item_kind item == 2i
         then [TasmBinding (tasm_item_label item) sec
                 (if sec == TasmCode then pc else addr)]
         else []) ++
        tasm_resolver_labels_from (tasm_next_section sec item)
          (pc + tasm_code_delta sec item)
          (addr + tasm_data_delta sec item) rest))`);
PROOF static thm tasm_resolver_labels_def = new_fun_definition(
    `tasm_resolver_labels (items:(tasm_item)list) : (tasm_binding)list =
       tasm_resolver_labels_from TasmCode 0i 8i items`);
PROOF static thm tasm_resolver_label_found_def = new_fun_definition(
    `tasm_resolver_label_found (items:(tasm_item)list) (label:int) : bool =
       tasm_binding_found label (tasm_resolver_labels items)`);
PROOF static thm tasm_resolver_label_section_def = new_fun_definition(
    `tasm_resolver_label_section (items:(tasm_item)list)
       (label:int) : tasm_section =
       tasm_binding_section
         (tasm_binding_lookup label (tasm_resolver_labels items))`);
PROOF static thm tasm_resolver_label_address_def = new_fun_definition(
    `tasm_resolver_label_address (items:(tasm_item)list)
       (label:int) : int =
       tasm_binding_addr
         (tasm_binding_lookup label (tasm_resolver_labels items))`);
PROOF thm tasm_label_found_def = new_fun_definition(
    `tasm_label_found (items:(tasm_item)list) (label:int) : bool =
       tasm_binding_found label (tasm_labels items)`);
PROOF thm tasm_label_section_def = new_fun_definition(
    `tasm_label_section (items:(tasm_item)list) (label:int)
       : tasm_section =
       tasm_binding_section
         (tasm_binding_lookup label (tasm_labels items))`);
PROOF thm tasm_label_address_def = new_fun_definition(
    `tasm_label_address (items:(tasm_item)list) (label:int) : int =
       tasm_binding_addr
         (tasm_binding_lookup label (tasm_labels items))`);
PROOF thm tasm_label_denotes_def = new_fun_definition(
    `tasm_label_denotes (items:(tasm_item)list) (label:int)
       (sec:tasm_section) (addr:int) : bool =
       (tasm_label_found items label &&
        tasm_label_section items label == sec &&
        tasm_label_address items label == addr)`);

PROOF int _e_tasm_labels = cst_add_const_to_header(`tasm_labels`);
PROOF int _e_tasm_binding_found =
    cst_add_const_to_header(`tasm_binding_found`);
PROOF int _e_tasm_binding_lookup =
    cst_add_const_to_header(`tasm_binding_lookup`);
PROOF int _e_tasm_label_found =
    cst_add_const_to_header(`tasm_label_found`);
PROOF int _e_tasm_label_section =
    cst_add_const_to_header(`tasm_label_section`);
PROOF int _e_tasm_label_address =
    cst_add_const_to_header(`tasm_label_address`);
PROOF int _e_tasm_label_denotes =
    cst_add_const_to_header(`tasm_label_denotes`);

PROOF thm tasm_entry_count_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_entry_count ([]:(tasm_item)list) = 0i) &&
     (!item rest.
       tasm_entry_count ((item:tasm_item) :: rest) =
         (if tasm_item_kind item == 1i then 1i else 0i) +
         tasm_entry_count rest)`);
PROOF thm tasm_entry_label_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_entry_label ([]:(tasm_item)list) = --1i) &&
     (!item rest.
       tasm_entry_label ((item:tasm_item) :: rest) =
         (if tasm_item_kind item == 1i
          then tasm_item_label item else tasm_entry_label rest))`);
PROOF thm tasm_last_line_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_last_line ([]:(tasm_item)list) = 0i) &&
     (!item rest.
       tasm_last_line ((item:tasm_item) :: rest) =
         (if rest == [] then tasm_item_line item
          else tasm_last_line rest))`);
PROOF thm tasm_label_count_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_label_count (label:int) ([]:(tasm_item)list) = 0i) &&
     (!label item rest.
       tasm_label_count (label:int) ((item:tasm_item) :: rest) =
         (if tasm_item_kind item == 2i &&
             tasm_item_label item == label
          then 1i else 0i) +
         tasm_label_count label rest)`);
PROOF thm tasm_lines_after_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_lines_after (previous:int) ([]:(tasm_item)list) = T) &&
     (!previous item rest.
       tasm_lines_after (previous:int) ((item:tasm_item) :: rest) <=>
         (previous < tasm_item_line item &&
          tasm_lines_after (tasm_item_line item) rest))`);
PROOF thm tasm_item_ids_ok_def = new_fun_definition(
    `tasm_item_ids_ok (item:tasm_item) : bool =
       (((tasm_item_kind item == 1i || tasm_item_kind item == 2i) ==>
           0i <= tasm_item_label item) &&
        (tasm_item_kind item == 3i &&
         (tasm_operand_kind (tasm_item_operand item) == 2i ||
          tasm_operand_kind (tasm_item_operand item) == 3i) ==>
           0i <= tasm_operand_value (tasm_item_operand item)))`);
PROOF thm tasm_items_ids_ok_def = new_fun_definition(
    `tasm_items_ids_ok (items:(tasm_item)list) : bool =
       (!i. 0i <= i ==> i < ilength items ==>
          tasm_item_ids_ok (inth i items))`);
PROOF thm tasm_items_wf_def = new_fun_definition(
    `tasm_items_wf (items:(tasm_item)list) : bool =
       (tasm_lines_after 0i items && tasm_items_ids_ok items)`);
PROOF thm tasm_int_seen_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_int_seen (needle:int) ([]:(int)list) = F) &&
     (!needle head rest.
       tasm_int_seen (needle:int) ((head:int) :: rest) <=>
         (head == needle || tasm_int_seen needle rest))`);
PROOF thm tasm_unique_from_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!seen. tasm_unique_from (seen:(int)list)
        ([]:(tasm_item)list) = T) &&
     (!seen item rest.
       tasm_unique_from (seen:(int)list)
         ((item:tasm_item) :: rest) <=>
       (if tasm_item_kind item == 2i
        then ~(tasm_int_seen (tasm_item_label item) seen) &&
             tasm_unique_from (tasm_item_label item :: seen) rest
        else tasm_unique_from seen rest))`);
PROOF thm tasm_labels_unique_def = new_fun_definition(
    `tasm_labels_unique (items:(tasm_item)list) : bool =
       tasm_unique_from [] items`);

PROOF int _e_tasm_entry_count =
    cst_add_const_to_header(`tasm_entry_count`);
PROOF int _e_tasm_entry_label =
    cst_add_const_to_header(`tasm_entry_label`);
PROOF int _e_tasm_last_line =
    cst_add_const_to_header(`tasm_last_line`);
PROOF int _e_tasm_label_count =
    cst_add_const_to_header(`tasm_label_count`);
PROOF int _e_tasm_items_wf =
    cst_add_const_to_header(`tasm_items_wf`);
PROOF int _e_tasm_labels_unique =
    cst_add_const_to_header(`tasm_labels_unique`);

PROOF thm tasm_values_signed_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_values_signed ([]:(int)list) = T) &&
     (!word rest.
       tasm_values_signed ((word:int) :: rest) <=>
         (tower_signed64 word && tasm_values_signed rest))`);
PROOF thm tasm_values_bytes_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_values_bytes ([]:(int)list) = T) &&
     (!byte rest.
       tasm_values_bytes ((byte:int) :: rest) <=>
         (tower_byte_value byte && tasm_values_bytes rest))`);
PROOF thm tasm_operand_form_ok_def = new_fun_definition(
    `tasm_operand_form_ok (op:tvm_opcode)
       (operand:tasm_operand) : bool =
       (if op == TVMPushOp
        then (tasm_operand_kind operand == 1i ||
              tasm_operand_kind operand == 3i)
        else if tvm_opcode_is_target op
        then (tasm_operand_kind operand == 1i ||
              tasm_operand_kind operand == 2i)
        else tasm_operand_kind operand == 0i)`);
PROOF thm tasm_operand_ref_ok_def = new_fun_definition(
    `tasm_operand_ref_ok (items:(tasm_item)list)
       (operand:tasm_operand) : bool =
       (if tasm_operand_kind operand == 2i
        then tasm_label_found items (tasm_operand_value operand) &&
             tasm_label_section items (tasm_operand_value operand) ==
               TasmCode
        else if tasm_operand_kind operand == 3i
        then tasm_label_found items (tasm_operand_value operand) &&
             tasm_label_section items (tasm_operand_value operand) ==
               TasmData
        else T)`);
PROOF thm tasm_operand_signed_ok_def = new_fun_definition(
    `tasm_operand_signed_ok (operand:tasm_operand) : bool =
       (tasm_operand_kind operand == 1i ==>
          tower_signed64 (tasm_operand_value operand))`);
PROOF thm tasm_item_semantic_ok_def = new_fun_definition(
    `tasm_item_semantic_ok (items:(tasm_item)list)
       (sec:tasm_section) (item:tasm_item) : bool =
       ((tasm_item_kind item == 3i ==> sec == TasmCode) &&
        ((tasm_item_kind item == 4i ||
          tasm_item_kind item == 5i ||
          tasm_item_kind item == 6i ||
          tasm_item_kind item == 7i) ==> sec == TasmData) &&
        (tasm_item_kind item == 3i ==>
          tasm_operand_form_ok (tasm_item_opcode item)
            (tasm_item_operand item) &&
          tasm_operand_ref_ok items (tasm_item_operand item) &&
          tasm_operand_signed_ok (tasm_item_operand item)) &&
        (tasm_item_kind item == 4i ==>
          tasm_values_signed (tasm_item_values item)) &&
        ((tasm_item_kind item == 5i ||
          tasm_item_kind item == 6i) ==>
          tasm_values_bytes (tasm_item_values item)) &&
        (tasm_item_kind item == 7i ==> 0i <= tasm_item_count item))`);
PROOF thm tasm_semantic_items_from_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!items sec.
       tasm_semantic_items_from (items:(tasm_item)list)
         (sec:tasm_section) [] = T) &&
     (!items sec item rest.
       tasm_semantic_items_from (items:(tasm_item)list)
         (sec:tasm_section) ((item:tasm_item) :: rest) <=>
       (tasm_item_semantic_ok items sec item &&
        tasm_semantic_items_from items
          (tasm_next_section sec item) rest))`);
PROOF thm tasm_semantic_ok_def = new_fun_definition(
    `tasm_semantic_ok (items:(tasm_item)list) : bool =
       (tasm_labels_unique items &&
        tasm_entry_count items == 1i &&
        tasm_label_found items (tasm_entry_label items) &&
        tasm_label_section items (tasm_entry_label items) == TasmCode &&
        tasm_semantic_items_from items TasmCode items)`);

PROOF int _e_tasm_values_signed =
    cst_add_const_to_header(`tasm_values_signed`);
PROOF int _e_tasm_values_bytes =
    cst_add_const_to_header(`tasm_values_bytes`);
PROOF int _e_tasm_operand_form_ok =
    cst_add_const_to_header(`tasm_operand_form_ok`);
PROOF int _e_tasm_operand_ref_ok =
    cst_add_const_to_header(`tasm_operand_ref_ok`);
PROOF int _e_tasm_semantic_ok =
    cst_add_const_to_header(`tasm_semantic_ok`);

PROOF thm tasm_resolved_immediate_def = new_fun_definition(
    `tasm_resolved_immediate (items:(tasm_item)list)
       (operand:tasm_operand) : int =
       (if tasm_operand_kind operand == 0i then 0i
        else if tasm_operand_kind operand == 1i
        then tasm_operand_value operand
        else tasm_label_address items (tasm_operand_value operand))`);
PROOF thm tasm_code_image_from_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!items sec.
       tasm_code_image_from (items:(tasm_item)list)
         (sec:tasm_section) [] = []) &&
     (!items sec item rest.
       tasm_code_image_from (items:(tasm_item)list)
         (sec:tasm_section) ((item:tasm_item) :: rest) =
       ((if sec == TasmCode && tasm_item_kind item == 3i
         then [TVMInst (tasm_item_opcode item)
                 (tasm_resolved_immediate items
                   (tasm_item_operand item))]
         else []) ++
        tasm_code_image_from items
          (tasm_next_section sec item) rest))`);
PROOF thm tasm_code_image_def = new_fun_definition(
    `tasm_code_image (items:(tasm_item)list) : (tvm_inst)list =
       tasm_code_image_from items TasmCode items`);

PROOF static thm tasm_resolver_resolved_immediate_def =
    new_fun_definition(
      `tasm_resolver_resolved_immediate (items:(tasm_item)list)
         (operand:tasm_operand) : int =
         (if tasm_operand_kind operand == 0i then 0i
          else if tasm_operand_kind operand == 1i
          then tasm_operand_value operand
          else tasm_resolver_label_address items
            (tasm_operand_value operand))`);
PROOF static thm tasm_resolver_code_image_from_def =
    new_rec_definition(
      get_theorem_by_name("list_RECURSION"),
      `(!items sec.
         tasm_resolver_code_image_from (items:(tasm_item)list)
           (sec:tasm_section) [] = []) &&
       (!items sec item rest.
         tasm_resolver_code_image_from (items:(tasm_item)list)
           (sec:tasm_section) ((item:tasm_item) :: rest) =
         ((if sec == TasmCode && tasm_item_kind item == 3i
           then [TVMInst (tasm_item_opcode item)
                   (tasm_resolver_resolved_immediate items
                     (tasm_item_operand item))]
           else []) ++
          tasm_resolver_code_image_from items
            (tasm_next_section sec item) rest))`);
PROOF static thm tasm_resolver_code_image_def = new_fun_definition(
    `tasm_resolver_code_image
       (items:(tasm_item)list) : (tvm_inst)list =
       tasm_resolver_code_image_from items TasmCode items`);

PROOF thm tasm_patch_bytes_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_patch_bytes (addr:int) ([]:(int)list) = []) &&
     (!addr byte rest.
       tasm_patch_bytes (addr:int) ((byte:int) :: rest) =
         TVMPatch addr byte :: tasm_patch_bytes (addr + 1i) rest)`);
PROOF thm tasm_patch_words_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_patch_words (addr:int) ([]:(int)list) = []) &&
     (!addr value rest.
       tasm_patch_words (addr:int) ((value:int) :: rest) =
         tasm_patch_bytes addr (tower_word_bytes value) ++
         tasm_patch_words (addr + 8i) rest)`);
PROOF thm tasm_data_patches_from_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_data_patches_from (sec:tasm_section) (addr:int)
        ([]:(tasm_item)list) = []) &&
     (!sec addr item rest.
       tasm_data_patches_from (sec:tasm_section) (addr:int)
         ((item:tasm_item) :: rest) =
       ((if sec == TasmData && tasm_item_kind item == 4i
         then tasm_patch_words addr (tasm_item_values item)
         else if sec == TasmData && tasm_item_kind item == 5i
         then tasm_patch_bytes addr (tasm_item_values item)
         else if sec == TasmData && tasm_item_kind item == 6i
         then tasm_patch_bytes addr (tasm_item_values item ++ [0i])
         else []) ++
        tasm_data_patches_from (tasm_next_section sec item)
          (addr + tasm_data_delta sec item) rest))`);
PROOF thm tasm_data_patches_def = new_fun_definition(
    `tasm_data_patches (items:(tasm_item)list) : (tvm_patch)list =
       tasm_data_patches_from TasmCode 8i items`);
PROOF thm tasm_object_image_def = new_fun_definition(
    `tasm_object_image (items:(tasm_item)list) : tvm_object =
       TVMObject
         (tasm_label_address items (tasm_entry_label items))
         (tasm_code_image items) (tasm_data_patches items)`);
PROOF static thm tasm_resolver_object_image_def = new_fun_definition(
    `tasm_resolver_object_image
       (items:(tasm_item)list) : tvm_object =
       TVMObject
         (tasm_resolver_label_address items (tasm_entry_label items))
         (tasm_resolver_code_image items) (tasm_data_patches items)`);

PROOF int _e_tasm_resolved_immediate =
    cst_add_const_to_header(`tasm_resolved_immediate`);
PROOF int _e_tasm_code_image =
    cst_add_const_to_header(`tasm_code_image`);
PROOF int _e_tasm_patch_bytes =
    cst_add_const_to_header(`tasm_patch_bytes`);
PROOF int _e_tasm_patch_words =
    cst_add_const_to_header(`tasm_patch_words`);
PROOF int _e_tasm_data_patches =
    cst_add_const_to_header(`tasm_data_patches`);
PROOF int _e_tasm_object_image =
    cst_add_const_to_header(`tasm_object_image`);

PROOF thm tasm_denotes_def = new_fun_definition(
    `tasm_denotes (items:(tasm_item)list) (obj:tvm_object) : bool =
       (tasm_items_wf items &&
        tasm_semantic_ok items &&
        obj == tasm_object_image items)`);
PROOF thm tasm_word_denotes_def = new_fun_definition(
    `tasm_word_denotes (items:(tasm_item)list) (line:int)
       (values:(int)list) (patches:(tvm_patch)list) : bool =
       (?before after.
          items == before ++ (TasmWord line values :: after) &&
          tasm_end_section TasmCode before == TasmData &&
          patches ==
            tasm_patch_words
              (8i + tasm_data_width_from TasmCode before) values)`);
PROOF thm tasm_space_denotes_def = new_fun_definition(
    `tasm_space_denotes (items:(tasm_item)list) (line:int)
       (count:int) (before_addr:int) (after_addr:int) : bool =
       (?before after.
          items == before ++ (TasmSpace line count :: after) &&
          tasm_end_section TasmCode before == TasmData &&
          before_addr == 8i + tasm_data_width_from TasmCode before &&
          after_addr == before_addr + count)`);
PROOF thm tasm_wrong_section_def = new_fun_definition(
    `tasm_wrong_section (items:(tasm_item)list) : bool =
       ~(tasm_semantic_items_from items TasmCode items)`);

PROOF int _e_tasm_denotes = cst_add_const_to_header(`tasm_denotes`);
PROOF int _e_tasm_word_denotes =
    cst_add_const_to_header(`tasm_word_denotes`);
PROOF int _e_tasm_space_denotes =
    cst_add_const_to_header(`tasm_space_denotes`);
PROOF int _e_tasm_wrong_section =
    cst_add_const_to_header(`tasm_wrong_section`);

PROOF static conv tasm_reduce_rewrite(const thm_list ths) {
  return then_conv(rewrite_conv(ths),
                   get_conversion_by_name("INT_REDUCE_CONV"));
}

PROOF thm tasm_error_le_def = new_fun_definition(
    `tasm_error_le (left:tasm_error) (right:tasm_error) : bool =
       (tasm_error_line left < tasm_error_line right ||
        (tasm_error_line left == tasm_error_line right &&
         tasm_error_rank left <= tasm_error_rank right))`);
PROOF thm tasm_error_min_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_error_min ([]:(tasm_error)list) = TasmError 1i 3i) &&
     (!err rest.
       tasm_error_min ((err:tasm_error) :: rest) =
         (if rest == [] then err
          else if tasm_error_le err (tasm_error_min rest)
          then err else tasm_error_min rest))`);
PROOF thm tasm_candidate_def = new_fun_definition(
    `tasm_candidate (bad:bool) (line:int) (rank:int)
       : (tasm_error)list =
       (if bad then [TasmError line rank] else [])`);
PROOF thm tasm_signed_candidates_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_signed_candidates (line:int) ([]:(int)list) = []) &&
     (!line value rest.
       tasm_signed_candidates (line:int) ((value:int) :: rest) =
         tasm_candidate (~(tower_signed64 value)) line 7i ++
         tasm_signed_candidates line rest)`);
PROOF thm tasm_byte_candidates_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(tasm_byte_candidates (line:int) ([]:(int)list) = []) &&
     (!line value rest.
       tasm_byte_candidates (line:int) ((value:int) :: rest) =
         tasm_candidate (~(tower_byte_value value)) line 8i ++
         tasm_byte_candidates line rest)`);

PROOF thm tasm_pass1_candidates_from_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!sec seen entry_seen.
       tasm_pass1_candidates_from (sec:tasm_section)
         (seen:(tasm_binding)list) (entry_seen:bool)
         ([]:(tasm_item)list) = []) &&
     (!sec seen entry_seen item rest.
       tasm_pass1_candidates_from (sec:tasm_section)
         (seen:(tasm_binding)list) (entry_seen:bool)
         ((item:tasm_item) :: rest) =
       (tasm_candidate
          (tasm_item_kind item == 2i &&
           tasm_binding_found (tasm_item_label item) seen)
          (tasm_item_line item) 0i ++
        tasm_candidate
          (tasm_item_kind item == 1i && entry_seen)
          (tasm_item_line item) 1i ++
        tasm_candidate
          ((tasm_item_kind item == 3i && ~(sec == TasmCode)) ||
           ((tasm_item_kind item == 4i ||
             tasm_item_kind item == 5i ||
             tasm_item_kind item == 6i ||
             tasm_item_kind item == 7i) && ~(sec == TasmData)))
          (tasm_item_line item) 2i ++
        (if tasm_item_kind item == 3i &&
            tasm_operand_kind (tasm_item_operand item) == 1i
         then tasm_signed_candidates (tasm_item_line item)
                [tasm_operand_value (tasm_item_operand item)]
         else []) ++
        (if tasm_item_kind item == 4i
         then tasm_signed_candidates (tasm_item_line item)
                (tasm_item_values item)
         else []) ++
        (if tasm_item_kind item == 5i ||
            tasm_item_kind item == 6i
         then tasm_byte_candidates (tasm_item_line item)
                (tasm_item_values item)
         else []) ++
        tasm_candidate
          (tasm_item_kind item == 7i && tasm_item_count item < 0i)
          (tasm_item_line item) 9i ++
        tasm_pass1_candidates_from (tasm_next_section sec item)
          ((if tasm_item_kind item == 2i
            then [TasmBinding (tasm_item_label item) sec 0i]
            else []) ++ seen)
          (entry_seen || tasm_item_kind item == 1i) rest))`);
PROOF thm tasm_pass1_candidates_def = new_fun_definition(
    `tasm_pass1_candidates (items:(tasm_item)list)
       : (tasm_error)list =
       (tasm_pass1_candidates_from TasmCode [] F items ++
        tasm_candidate (tasm_entry_count items == 0i)
          (tasm_last_line items + 1i) 3i)`);

PROOF thm tasm_reference_candidates_def = new_fun_definition(
    `tasm_reference_candidates (items:(tasm_item)list)
       (line:int) (operand:tasm_operand) : (tasm_error)list =
       (if tasm_operand_kind operand == 2i
        then if ~(tasm_resolver_label_found items
                    (tasm_operand_value operand))
             then [TasmError line 4i]
             else tasm_candidate
               (~(tasm_resolver_label_section items
                    (tasm_operand_value operand) == TasmCode))
               line 5i
        else if tasm_operand_kind operand == 3i
        then if ~(tasm_resolver_label_found items
                    (tasm_operand_value operand))
             then [TasmError line 4i]
             else tasm_candidate
               (~(tasm_resolver_label_section items
                    (tasm_operand_value operand) == TasmData))
               line 5i
        else [])`);
PROOF thm tasm_pass2_candidates_from_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!items.
       tasm_pass2_candidates_from (items:(tasm_item)list)
         ([]:(tasm_item)list) = []) &&
     (!items item rest.
       tasm_pass2_candidates_from (items:(tasm_item)list)
         ((item:tasm_item) :: rest) =
       ((if tasm_item_kind item == 1i
         then if ~(tasm_resolver_label_found items
                    (tasm_item_label item))
              then [TasmError (tasm_item_line item) 4i]
              else tasm_candidate
                (~(tasm_resolver_label_section items
                     (tasm_item_label item) == TasmCode))
                (tasm_item_line item) 5i
         else []) ++
        (if tasm_item_kind item == 3i
         then tasm_candidate
                (~(tasm_operand_form_ok (tasm_item_opcode item)
                    (tasm_item_operand item)))
                (tasm_item_line item) 6i ++
              tasm_reference_candidates items (tasm_item_line item)
                (tasm_item_operand item)
         else []) ++
        tasm_pass2_candidates_from items rest))`);
PROOF thm tasm_pass2_candidates_def = new_fun_definition(
    `tasm_pass2_candidates (items:(tasm_item)list)
       : (tasm_error)list =
       tasm_pass2_candidates_from items items`);
PROOF thm tasm_candidates_def = new_fun_definition(
    `tasm_candidates (items:(tasm_item)list) : (tasm_error)list =
       tasm_pass1_candidates items ++ tasm_pass2_candidates items`);
PROOF thm tasm_selected_error_def = new_fun_definition(
    `tasm_selected_error (items:(tasm_item)list) : tasm_error =
       (if tasm_candidates items == []
        then TasmError (tasm_last_line items + 1i) 3i
        else tasm_error_min (tasm_candidates items))`);
PROOF thm tasm_resolve_def = new_fun_definition(
    `tasm_resolve (items:(tasm_item)list) : tasm_result =
       (if tasm_candidates items == [] && tasm_semantic_ok items
        then TasmOk (tasm_resolver_object_image items)
        else TasmFail
          (tasm_error_line (tasm_selected_error items))
          (tasm_error_rank (tasm_selected_error items)))`);

PROOF int _e_tasm_error_le =
    cst_add_const_to_header(`tasm_error_le`);
PROOF int _e_tasm_error_min =
    cst_add_const_to_header(`tasm_error_min`);
PROOF int _e_tasm_pass1_candidates =
    cst_add_const_to_header(`tasm_pass1_candidates`);
PROOF int _e_tasm_pass2_candidates =
    cst_add_const_to_header(`tasm_pass2_candidates`);
PROOF int _e_tasm_candidates =
    cst_add_const_to_header(`tasm_candidates`);
PROOF int _e_tasm_selected_error =
    cst_add_const_to_header(`tasm_selected_error`);
PROOF int _e_tasm_resolve = cst_add_const_to_header(`tasm_resolve`);

PROOF static thm tasm_prove_resolver_labels_from_eq(void) {
  gnode root = gnode_new_with_ccl(
      `!(source:(tasm_item)list) (sec:tasm_section) (pc:int) (addr:int).
         tasm_resolver_labels_from sec pc addr source ==
         tasm_labels_from sec pc addr source`);
  gnode_list cases = INDUCT_TAC(root, `source:(tasm_item)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        tasm_resolver_labels_from_def, tasm_labels_from_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        tasm_resolver_labels_from_def, tasm_labels_from_def));
  }
  return gnode_prove(root);
}
PROOF static thm tasm_resolver_labels_from_eq =
    tasm_prove_resolver_labels_from_eq();

PROOF static thm tasm_prove_resolver_labels_eq(void) {
  gnode root = gnode_new_with_ccl(
      `!(items:(tasm_item)list).
         tasm_resolver_labels items == tasm_labels items`);
  CONV_TAC(root, reduce_rewrite_conv(THM_LIST(
      tasm_resolver_labels_def, tasm_labels_def,
      tasm_resolver_labels_from_eq)));
  return gnode_prove(root);
}
PROOF static thm tasm_resolver_labels_eq =
    tasm_prove_resolver_labels_eq();

PROOF static thm tasm_prove_resolver_label_address_eq(void) {
  gnode root = gnode_new_with_ccl(
      `!(items:(tasm_item)list) (label:int).
         tasm_resolver_label_address items label ==
         tasm_label_address items label`);
  CONV_TAC(root, reduce_rewrite_conv(THM_LIST(
      tasm_resolver_label_address_def, tasm_label_address_def,
      tasm_resolver_labels_eq)));
  return gnode_prove(root);
}
PROOF static thm tasm_resolver_label_address_eq =
    tasm_prove_resolver_label_address_eq();

PROOF static thm tasm_prove_resolver_immediate_eq(void) {
  gnode root = gnode_new_with_ccl(
      `!(items:(tasm_item)list) (operand:tasm_operand).
         tasm_resolver_resolved_immediate items operand ==
         tasm_resolved_immediate items operand`);
  CONV_TAC(root, reduce_rewrite_conv(THM_LIST(
      tasm_resolver_resolved_immediate_def, tasm_resolved_immediate_def,
      tasm_resolver_label_address_eq)));
  return gnode_prove(root);
}
PROOF static thm tasm_resolver_immediate_eq =
    tasm_prove_resolver_immediate_eq();

PROOF static thm tasm_prove_resolver_code_image_from_eq(void) {
  gnode root = gnode_new_with_ccl(
      `!(source:(tasm_item)list) (items:(tasm_item)list)
         (sec:tasm_section).
         tasm_resolver_code_image_from items sec source ==
         tasm_code_image_from items sec source`);
  gnode_list cases = INDUCT_TAC(root, `source:(tasm_item)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        tasm_resolver_code_image_from_def, tasm_code_image_from_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        tasm_resolver_code_image_from_def, tasm_code_image_from_def,
        tasm_resolver_immediate_eq));
  }
  return gnode_prove(root);
}
PROOF static thm tasm_resolver_code_image_from_eq =
    tasm_prove_resolver_code_image_from_eq();

PROOF static thm tasm_prove_resolver_code_image_eq(void) {
  gnode root = gnode_new_with_ccl(
      `!(items:(tasm_item)list).
         tasm_resolver_code_image items == tasm_code_image items`);
  CONV_TAC(root, reduce_rewrite_conv(THM_LIST(
      tasm_resolver_code_image_def, tasm_code_image_def,
      tasm_resolver_code_image_from_eq)));
  return gnode_prove(root);
}
PROOF static thm tasm_resolver_code_image_eq =
    tasm_prove_resolver_code_image_eq();

PROOF static thm tasm_prove_resolver_object_image_eq(void) {
  gnode root = gnode_new_with_ccl(
      `!(items:(tasm_item)list).
         tasm_resolver_object_image items == tasm_object_image items`);
  CONV_TAC(root, reduce_rewrite_conv(THM_LIST(
      tasm_resolver_object_image_def, tasm_object_image_def,
      tasm_resolver_label_address_eq, tasm_resolver_code_image_eq)));
  return gnode_prove(root);
}
PROOF static thm tasm_resolver_object_image_eq =
    tasm_prove_resolver_object_image_eq();

PROOF thm mk_tasm_resolve_deterministic(void) {
  gnode root = gnode_new_with_ccl(
      `!items result1 result2.
         tasm_resolve (items:(tasm_item)list) ==
           (result1:tasm_result) ==>
         tasm_resolve items == (result2:tasm_result) ==>
         result1 == result2`);
  gnode leaf = AUTO_INTROS_TAC(root);
  labeled_term_list as = goal_lasmps(leaf->g);
  ACCEPT_TAC(leaf, trans_rule(
      sym_rule(assume_rule(as[0].tm)), assume_rule(as[1].tm)));
  return gnode_prove(root);
}
PROOF thm tasm_resolve_deterministic =
    mk_tasm_resolve_deterministic();

PROOF thm mk_tasm_resolve_sound(void) {
  gnode root = gnode_new_with_ccl(
      `!items obj.
         tasm_items_wf (items:(tasm_item)list) &&
         tasm_resolve items == TasmOk (obj:tvm_object) ==>
         tasm_denotes items obj`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm both = assume_rule(goal_lasmps(leaf->g)[0].tm);
  gnode_list cases = BOOL_CASES_TAC(leaf,
      `tasm_candidates (items:(tasm_item)list) == [] &&
       tasm_semantic_ok items`, "Hok");
  {
    thm cond = assume_rule(goal_lasmps(cases[0]->g)[1].tm);
    thm resolved = conv_rule(rewrite_conv(THM_LIST(
        tasm_resolve_def, cond)), conjunct2_rule(both));
    thm image_eq = conv_rule(rewrite_conv(THM_LIST(
        get_datatype_injectivity("tasm_result"))), resolved);
    thm semantic_image = spec_rule(
        `items:(tasm_item)list`, tasm_resolver_object_image_eq);
    thm object_image = trans_rule(sym_rule(image_eq), semantic_image);
    thm rhs = conj_rule(conjunct1_rule(both),
        conj_rule(conjunct2_rule(cond), object_image));
    thm defeq = inst_rule(TERM_PAIR_LIST(
        (term_pair){`items:(tasm_item)list`, `items:(tasm_item)list`},
        (term_pair){`obj:tvm_object`, `obj:tvm_object`}),
        tasm_denotes_def);
    ACCEPT_TAC(cases[0], eq_mp_rule(sym_rule(defeq), rhs));
  }
  {
    thm bad = assume_rule(goal_lasmps(cases[1]->g)[1].tm);
    thm impossible = conv_rule(tasm_reduce_rewrite(
        THM_LIST(tasm_resolve_def, bad,
          get_datatype_distinctness("tasm_result"))),
        conjunct2_rule(both));
    CONTR_TAC(cases[1], impossible);
  }
  return gnode_prove(root);
}
PROOF thm tasm_resolve_sound = mk_tasm_resolve_sound();

PROOF thm tasm_data_fits_def = new_fun_definition(
    `tasm_data_fits (items:(tasm_item)list) : bool =
       (8i + tasm_data_width items <= 1048576i &&
        tvm_patches_valid (tasm_data_patches items) &&
        tvm_code_shape (tasm_code_image items) &&
        tvm_target_valid (tasm_code_image items)
          (tasm_label_address items (tasm_entry_label items)) &&
        tvm_targets_valid (tasm_code_image items))`);
PROOF int _e_tasm_data_fits =
    cst_add_const_to_header(`tasm_data_fits`);

PROOF thm mk_tasm_denotes_object_wf(void) {
  thm den = pure_rewrite_rule(THM_LIST(tasm_denotes_def),
      assume_rule(
        `tasm_denotes (items:(tasm_item)list) (obj:tvm_object)`));
  thm fits = pure_rewrite_rule(THM_LIST(tasm_data_fits_def),
      assume_rule(`tasm_data_fits (items:(tasm_item)list)`));
  thm tail1 = conjunct2_rule(fits);
  thm patches = conjunct1_rule(tail1);
  thm tail2 = conjunct2_rule(tail1);
  thm shape = conjunct1_rule(tail2);
  thm tail3 = conjunct2_rule(tail2);
  thm entry = conjunct1_rule(tail3);
  thm targets = conjunct2_rule(tail3);
  thm rhs = conj_rule(conj_rule(patches, shape),
      conj_rule(entry, targets));
  thm image_wf_eq = apply_conversion(pure_rewrite_conv(THM_LIST(
      tasm_object_image_def, get_tvm_object_wf_def(),
      get_tvm_load_ok_def(), get_tvm_object_entry_def(),
      get_tvm_object_code_def(), get_tvm_object_patches_def())),
      `tvm_object_wf (tasm_object_image (items:(tasm_item)list))`);
  thm image_wf = eq_mp_rule(sym_rule(image_wf_eq), rhs);
  thm obj_eq = conjunct2_rule(conjunct2_rule(den));
  thm pred_eq = beta_norm(ap_term_rule(
      `\candidate:tvm_object. tvm_object_wf candidate`, obj_eq));
  thm result = eq_mp_rule(sym_rule(pred_eq), image_wf);
  return close_implication(
      `!items obj.
         tasm_denotes (items:(tasm_item)list) (obj:tvm_object) ==>
         tasm_data_fits items ==> tvm_object_wf obj`, result);
}
PROOF thm tasm_denotes_object_wf = mk_tasm_denotes_object_wf();

PROOF thm mk_tasm_code_label_inversion(void) {
  thm den = pure_rewrite_rule(THM_LIST(tasm_label_denotes_def),
      assume_rule(
        `tasm_label_denotes (items:(tasm_item)list) (label:int)
          TasmCode (addr:int)`));
  thm result = sym_rule(conjunct2_rule(conjunct2_rule(den)));
  return close_implication(
      `!items obj label addr.
         tasm_denotes (items:(tasm_item)list) (obj:tvm_object) ==>
         tasm_label_denotes items (label:int) TasmCode (addr:int) ==>
         addr == tasm_label_address items label`, result);
}
PROOF thm tasm_code_label_inversion = mk_tasm_code_label_inversion();

PROOF thm mk_tasm_word_inversion(void) {
  thm body = pure_rewrite_rule(THM_LIST(tasm_word_denotes_def),
      assume_rule(
        `tasm_word_denotes (items:(tasm_item)list) (line:int)
          (values:(int)list) (patches:(tvm_patch)list)`));
  return close_implication(
      `!items line values patches.
         tasm_word_denotes (items:(tasm_item)list) (line:int)
           (values:(int)list) (patches:(tvm_patch)list) ==>
         ?before after.
           items == before ++ (TasmWord line values :: after) &&
           tasm_end_section TasmCode before == TasmData &&
           patches ==
             tasm_patch_words
               (8i + tasm_data_width_from TasmCode before) values`,
      body);
}
PROOF thm tasm_word_inversion = mk_tasm_word_inversion();

PROOF thm mk_tasm_patch_words_one(void) {
  gnode root = gnode_new_with_ccl(
      `!addr value.
         tasm_patch_words (addr:int) [(value:int)] ==
         tasm_patch_bytes addr (tower_word_bytes value)`);
  CONV_TAC(root, rewrite_conv(THM_LIST(
      tasm_patch_words_def, get_theorem_by_name("APPEND"),
      get_theorem_by_name("APPEND_NIL"))));
  return gnode_prove(root);
}
PROOF thm tasm_patch_words_one = mk_tasm_patch_words_one();

PROOF thm mk_tasm_space_inversion(void) {
  thm body = pure_rewrite_rule(THM_LIST(tasm_space_denotes_def),
      assume_rule(
        `tasm_space_denotes (items:(tasm_item)list) (line:int)
          (count:int) (before_addr:int) (after_addr:int)`));
  return close_implication(
      `!items line count before_addr after_addr.
         tasm_space_denotes (items:(tasm_item)list) (line:int)
           (count:int) (before_addr:int) (after_addr:int) ==>
         ?before after.
           items == before ++ (TasmSpace line count :: after) &&
           tasm_end_section TasmCode before == TasmData &&
           before_addr ==
             8i + tasm_data_width_from TasmCode before &&
           after_addr == before_addr + count`, body);
}
PROOF thm tasm_space_inversion = mk_tasm_space_inversion();

PROOF thm mk_tasm_space_emits_none(void) {
  gnode root = gnode_new_with_ccl(
      `!addr line count rest.
         tasm_data_patches_from TasmData (addr:int)
           (TasmSpace (line:int) (count:int) :: (rest:(tasm_item)list)) ==
         tasm_data_patches_from TasmData (addr + count) rest`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm equation = specl_rule(TERM_LIST(
      `TasmData:tasm_section`, `addr:int`,
      `TasmSpace (line:int) (count:int)`, `rest:(tasm_item)list`),
      conjunct2_rule(tasm_data_patches_from_def));
  thm reduced = conv_rule(tasm_reduce_rewrite(THM_LIST(
      tasm_next_section_def, tasm_data_delta_def,
      tasm_item_kind_def, tasm_item_count_def,
      tasm_item_section_def)), equation);
  thm nil = ispec_rule(
      `tasm_data_patches_from TasmData
        ((addr:int) + (count:int)) (rest:(tasm_item)list)`,
      conjunct1_rule(get_theorem_by_name("APPEND")));
  ACCEPT_TAC(leaf, trans_rule(reduced, nil));
  return gnode_prove(root);
}
PROOF thm tasm_space_emits_none = mk_tasm_space_emits_none();

PROOF thm mk_tasm_wrong_section_no_denotation(void) {
  thm wrong = pure_rewrite_rule(THM_LIST(tasm_wrong_section_def),
      assume_rule(`tasm_wrong_section (items:(tasm_item)list)`));
  thm den = pure_rewrite_rule(THM_LIST(tasm_denotes_def),
      assume_rule(
        `tasm_denotes (items:(tasm_item)list) (obj:tvm_object)`));
  thm semantic = pure_rewrite_rule(THM_LIST(tasm_semantic_ok_def),
      conjunct1_rule(conjunct2_rule(den)));
  thm traced = conjunct2_rule(conjunct2_rule(
      conjunct2_rule(conjunct2_rule(semantic))));
  thm contradiction = contra(wrong, traced);
  thm negated = not_intro(
      `tasm_denotes (items:(tasm_item)list) (obj:tvm_object)`,
      contradiction);
  thm implication = disch_rule(
      `tasm_wrong_section (items:(tasm_item)list)`, negated);
  return gen_rule(`items:(tasm_item)list`,
      gen_rule(`obj:tvm_object`, implication));
}
PROOF thm tasm_wrong_section_no_denotation =
    mk_tasm_wrong_section_no_denotation();

PROOF thm mk_tasm_example_resolution(void) {
  gnode root = gnode_new_with_ccl(
      `tasm_resolve
         [TasmEntry 1i 0i;
          TasmLabel 2i 0i;
          TasmInstr 3i TVMPushOp (TasmDataRef 1i);
          TasmInstr 4i TVMLoadBOp TasmNoOperand;
          TasmInstr 5i TVMPutcOp TasmNoOperand;
          TasmInstr 6i TVMJmpOp (TasmCodeRef 2i);
          TasmSection 7i TasmData;
          TasmLabel 8i 1i;
          TasmByte 9i [65i];
          TasmSpace 10i 3i;
          TasmSection 11i TasmCode;
          TasmLabel 12i 2i;
          TasmInstr 13i TVMPushOp (TasmImm 0i);
          TasmInstr 14i TVMHaltOp TasmNoOperand] ==
       TasmOk
         (TVMObject 0i
           [TVMInst TVMPushOp 8i;
            TVMInst TVMLoadBOp 0i;
            TVMInst TVMPutcOp 0i;
            TVMInst TVMJmpOp 4i;
            TVMInst TVMPushOp 0i;
            TVMInst TVMHaltOp 0i]
           [TVMPatch 8i 65i])`);
  thm_list rules = THM_LIST(
      tasm_resolve_def, tasm_candidates_def,
      tasm_resolver_object_image_def,
      tasm_resolver_code_image_def,
      tasm_resolver_code_image_from_def,
      tasm_resolver_resolved_immediate_def,
      tasm_resolver_label_found_def,
      tasm_resolver_label_section_def,
      tasm_resolver_label_address_def,
      tasm_resolver_labels_def, tasm_resolver_labels_from_def,
      tasm_pass1_candidates_def, tasm_pass1_candidates_from_def,
      tasm_pass2_candidates_def, tasm_pass2_candidates_from_def,
      tasm_reference_candidates_def, tasm_candidate_def,
      tasm_signed_candidates_def, tasm_byte_candidates_def,
      tasm_semantic_ok_def, tasm_labels_unique_def,
      tasm_unique_from_def, tasm_int_seen_def,
      tasm_entry_count_def, tasm_entry_label_def,
      tasm_semantic_items_from_def, tasm_item_semantic_ok_def,
      tasm_operand_form_ok_def, tasm_operand_ref_ok_def,
      tasm_operand_signed_ok_def, tasm_values_signed_def,
      tasm_values_bytes_def, tasm_label_found_def,
      tasm_label_section_def, tasm_label_address_def,
      tasm_labels_def, tasm_labels_from_def,
      tasm_binding_found_def, tasm_binding_lookup_def,
      tasm_binding_id_def, tasm_binding_section_def,
      tasm_binding_addr_def, tasm_next_section_def,
      tasm_code_delta_def, tasm_data_delta_def,
      tasm_item_kind_def, tasm_item_section_def,
      tasm_item_label_def, tasm_item_line_def,
      tasm_item_opcode_def, tasm_item_operand_def,
      tasm_item_values_def, tasm_item_count_def,
      tasm_operand_kind_def, tasm_operand_value_def,
      get_tvm_opcode_is_target_def(), get_tvm_opcode_has_imm_def(),
      get_tower_signed64_def(), get_tower_byte_value_def(),
      tasm_object_image_def,
      tasm_code_image_def, tasm_code_image_from_def,
      tasm_resolved_immediate_def, tasm_data_patches_def,
      tasm_data_patches_from_def, tasm_patch_bytes_def,
      tasm_patch_words_def,
      conjunct1_rule(get_theorem_by_name("APPEND")),
      conjunct2_rule(get_theorem_by_name("APPEND")),
      get_theorem_by_name("APPEND_NIL"),
      get_datatype_distinctness("tasm_section"),
      get_datatype_distinctness("tasm_operand"),
      get_datatype_distinctness("tvm_opcode"));
  conv evaluation = tasm_reduce_rewrite(rules);
  conv pass = evaluation;
  for (size_t i = 1; i < 20; ++i) {
    evaluation = then_conv(evaluation, pass);
  }
  return eqt_elim_rule(apply_conversion(
      evaluation, goal_ccl(root->g)));
}
PROOF static thm tasm_example_resolve_equation =
    mk_tasm_example_resolution();

PROOF static term tasm_example_object(void) {
  return
      `TVMObject 0i
         [TVMInst TVMPushOp 8i;
          TVMInst TVMLoadBOp 0i;
          TVMInst TVMPutcOp 0i;
          TVMInst TVMJmpOp 4i;
          TVMInst TVMPushOp 0i;
          TVMInst TVMHaltOp 0i]
         [TVMPatch 8i 65i]`;
}

PROOF static thm tasm_nth_step(const term index) {
  thm successor = apply_conversion(
      get_conversion_by_name("NUM_SUC_CONV"),
      mk_comb(`SUC`, index));
  return conv_rule(rewrite_conv(THM_LIST(successor)),
      inst_rule(TERM_PAIR_LIST(
        (term_pair){index, `n:num`}),
        conjunct2_rule(get_theorem_by_name("NTH_DEF"))));
}

PROOF static thm tasm_prove_example_load_ok(void) {
  term object = tasm_example_object();
  gnode root = gnode_new_with_ccl(
      `tvm_load_ok (${object:tvm_object})`);
  gnode expanded = CONV_TAC(root, rewrite_conv(THM_LIST(
      get_tvm_load_ok_def(), get_tvm_object_code_def(),
      get_tvm_object_patches_def())));
  gnode_list parts = CONJ_TAC(expanded);
  {
    gnode indexed = CONV_TAC(parts[0], rewrite_conv(THM_LIST(
        get_tvm_patches_valid_def())));
    gnode leaf = AUTO_INTROS_TAC(indexed);
    thm lower = assume_rule(`0i <= (i:int)`);
    thm upper = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
        assume_rule(
          `(i:int) < ilength [TVMPatch 8i 65i]`));
    thm index_zero = mp_rule(mp_rule(int_arith_rule(
        `0i <= (i:int) ==> i < 1i ==> i == 0i`), lower), upper);
    gnode closed = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        index_zero, get_theorem_by_name("INTH_DEF"),
        get_theorem_by_name("NUM_OF_INT_OF_NUM"),
        get_theorem_by_name("NTH_DEF"),
        get_tvm_patch_valid_def(), get_tvm_patch_addr_def(),
        get_tvm_patch_byte_def(), get_tower_addr_valid_def(),
        get_tower_byte_value_def())));
    ENSURE_COND(!IS_NULL(closed->solved),
        "example patch validity remains open: %s", cstr_gnode(closed));
  }
  {
    gnode indexed = CONV_TAC(parts[1], rewrite_conv(THM_LIST(
        get_tvm_code_shape_def())));
    gnode leaf = AUTO_INTROS_TAC(indexed);
    thm lower = assume_rule(`0i <= (i:int)`);
    thm upper = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
        assume_rule(
          `(i:int) <
           ilength
             [TVMInst TVMPushOp 8i;
              TVMInst TVMLoadBOp 0i;
              TVMInst TVMPutcOp 0i;
              TVMInst TVMJmpOp 4i;
              TVMInst TVMPushOp 0i;
              TVMInst TVMHaltOp 0i]`));
    thm cases = mp_rule(mp_rule(int_arith_rule(
        `0i <= (i:int) ==> i < 6i ==>
         i == 0i || i == 1i || i == 2i ||
         i == 3i || i == 4i || i == 5i`), lower), upper);
    gnode_list branches = DISJ_CASES_TAC(
        leaf, cases, "Htasm_example_index");
    term_list equalities = TERM_LIST(
        `(i:int) == 0i`, `(i:int) == 1i`, `(i:int) == 2i`,
        `(i:int) == 3i`, `(i:int) == 4i`, `(i:int) == 5i`);
    for (size_t i = 0; i < 6; ++i) {
      conv normalize = reduce_rewrite_conv(THM_LIST(
          assume_rule(equalities[i]), get_theorem_by_name("INTH_DEF"),
          get_theorem_by_name("NUM_OF_INT_OF_NUM"),
          get_theorem_by_name("NTH_DEF"),
          tasm_nth_step(`0`), tasm_nth_step(`1`),
          tasm_nth_step(`2`), tasm_nth_step(`3`),
          tasm_nth_step(`4`),
          get_tvm_inst_shape_def(), get_tvm_inst_op_def(),
          get_tvm_inst_imm_def(), get_tvm_opcode_has_imm_def(),
          get_tower_signed64_def()));
      gnode closed = CONV_TAC(
          branches[i], then_conv(normalize, normalize));
      ENSURE_COND(!IS_NULL(closed->solved),
          "example instruction shape %zu remains open: %s",
          i, cstr_gnode(closed));
    }
  }
  return gnode_prove(root);
err:
  return empty_theorem;
}
PROOF static thm tasm_example_load_ok =
    tasm_prove_example_load_ok();

PROOF static thm tasm_iter_step(const term index) {
  thm successor = apply_conversion(
      get_conversion_by_name("NUM_SUC_CONV"),
      mk_comb(`SUC`, index));
  return conv_rule(rewrite_conv(THM_LIST(successor)),
      spec_rule(index, conjunct2_rule(get_tvm_iter_def())));
}

PROOF static thm_list tasm_example_tvm_rules(void) {
  thm_list rules = get_tvm_eval_defs();
  thm_list extra = THM_LIST(
      eqt_intro_rule(tasm_example_load_ok),
      get_tvm_push_transition(), get_tvm_loadb_transition(),
      get_tvm_putc_transition(), get_tvm_jmp_transition(),
      get_tvm_halt_transition(), get_tvm_action_task_def(),
      get_tvm_next_state_def(), get_tvm_jump_state_def(),
      get_tower_signed64_def(), get_tower_byte_value_def(),
      get_tower_addr_valid_def(), get_tower_u8_def(),
      get_tower_wrap64_def(), get_tower_zero_mem_def(),
      get_tower_getb_def(), get_tower_setb_def(),
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("APPEND_NIL"),
      get_theorem_by_name("ALL"),
      get_theorem_by_name("ILENGTH_DEF"),
      get_theorem_by_name("INTH_DEF"),
      get_theorem_by_name("NUM_OF_INT_OF_NUM"),
      get_theorem_by_name("NTH_DEF"),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"),
      tasm_nth_step(`0`), tasm_nth_step(`1`),
      tasm_nth_step(`2`), tasm_nth_step(`3`),
      tasm_nth_step(`4`), tasm_nth_step(`5`),
      tasm_iter_step(`0`), tasm_iter_step(`1`),
      tasm_iter_step(`2`), tasm_iter_step(`3`),
      tasm_iter_step(`4`), tasm_iter_step(`5`),
      tasm_iter_step(`6`));
  for (size_t i = 0; i < vector_size(extra); ++i) {
    vector_add(&rules, extra[i]);
  }
  return rules;
}

PROOF static thm tasm_compute_example_iteration(void) {
  term object = tasm_example_object();
  term boot = `TVMBoot (${object:tvm_object}) ([]:(int)list)`;
  thm_list rules = tasm_example_tvm_rules();
  conv pass = reduce_rewrite_conv(rules);
  conv evaluation = pass;
  for (size_t i = 1; i < 48; ++i) {
    evaluation = then_conv(evaluation, pass);
  }
  return apply_conversion(
      evaluation, mk_comb(mk_comb(`tvm_iter`, `7`), boot));
}
PROOF static thm tasm_example_iteration =
    tasm_compute_example_iteration();

PROOF static thm tasm_prove_example_execution(void) {
  term object = tasm_example_object();
  term boot = `TVMBoot (${object:tvm_object}) ([]:(int)list)`;
  thm_list rules = tasm_example_tvm_rules();
  conv pass = reduce_rewrite_conv(rules);
  conv evaluation = pass;
  for (size_t i = 1; i < 48; ++i) {
    evaluation = then_conv(evaluation, pass);
  }
  thm iteration = tasm_example_iteration;
  term done = dest_eq(concl(iteration)).tm2;
  dest_comb_results kind_app = dest_comb(done);
  term kind = kind_app.tm2;
  dest_comb_results status_app = dest_comb(kind_app.tm1);
  term status = status_app.tm2;
  term state = dest_comb(status_app.tm1).tm2;
  term outcome =
      `TVMOutcome (${state:tvm_state}) (${status:int}) (${kind:int})`;
  thm done_exec = ispecl_rule(
      TERM_LIST(state, status, kind), get_tvm_exec_done());
  thm iter_lift = beta_norm(ap_term_rule(
      `\task:tvm_task. tvm_exec task (${outcome:tvm_outcome})`,
      iteration));
  thm iter_exec = eq_mp_rule(sym_rule(iter_lift), done_exec);
  thm boot_exec = mp_rule(ispecl_rule(
      TERM_LIST(`7:num`, boot, outcome), get_tvm_exec_prefix()),
      iter_exec);
  thm valid_input = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules),
      `tvm_valid_input ([]:(int)list)`));
  thm status_byte = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules), `tower_byte_value 0i`));
  thm output_equal = eqt_elim_rule(apply_conversion(
      evaluation, `tvm_output (${state:tvm_state}) == [65i]`));
  gnode root = gnode_new_with_ccl(
      `tvm_terminates (${object:tvm_object})
         ([]:(int)list) [65i] 0i`);
  gnode expanded = CONV_TAC(root, rewrite_conv(THM_LIST(
      get_tvm_terminates_def())));
  gnode_list outer = CONJ_TAC(expanded);
  ACCEPT_TAC(outer[0], valid_input);
  gnode_list rest = CONJ_TAC(outer[1]);
  ACCEPT_TAC(rest[0], status_byte);
  gnode witness = EXISTS_TAC(rest[1], state);
  ACCEPT_TAC(witness, conj_rule(boot_exec, output_equal));
  return gnode_prove(root);
}
PROOF static thm tasm_example_execution =
    tasm_prove_example_execution();
PROOF thm tasm_example_resolution = conj_rule(
    tasm_example_resolve_equation, tasm_example_execution);


PROOF thm get_tasm_section_recursion(void) {
  return tasm_section_RECURSION;
}
PROOF thm get_tasm_operand_recursion(void) {
  return tasm_operand_RECURSION;
}
PROOF thm get_tasm_item_recursion(void) { return tasm_item_RECURSION; }
PROOF thm get_tasm_binding_recursion(void) {
  return tasm_binding_RECURSION;
}
PROOF thm get_tasm_result_recursion(void) {
  return tasm_result_RECURSION;
}
PROOF thm get_tasm_item_selectors_def(void) {
  return conj_rule(tasm_item_line_def,
      conj_rule(tasm_item_kind_def,
        conj_rule(tasm_item_section_def,
          conj_rule(tasm_item_label_def,
            conj_rule(tasm_item_opcode_def,
              conj_rule(tasm_item_operand_def,
                conj_rule(tasm_item_values_def,
                  tasm_item_count_def)))))));
}
PROOF thm get_tasm_trace_defs(void) {
  return conj_rule(tasm_end_section_def,
      conj_rule(tasm_code_width_from_def, tasm_data_width_from_def));
}
PROOF thm get_tasm_labels_def(void) { return tasm_labels_def; }
PROOF thm get_tasm_label_denotes_def(void) {
  return tasm_label_denotes_def;
}
PROOF thm get_tasm_items_wf_def(void) { return tasm_items_wf_def; }
PROOF thm get_tasm_semantic_ok_def(void) {
  return tasm_semantic_ok_def;
}
PROOF thm get_tasm_code_image_def(void) { return tasm_code_image_def; }
PROOF thm get_tasm_data_patches_def(void) {
  return tasm_data_patches_def;
}
PROOF thm get_tasm_object_image_def(void) {
  return tasm_object_image_def;
}
PROOF thm get_tasm_denotes_def(void) { return tasm_denotes_def; }
PROOF thm get_tasm_candidates_def(void) { return tasm_candidates_def; }
PROOF thm get_tasm_resolve_def(void) { return tasm_resolve_def; }
PROOF thm get_tasm_resolve_deterministic(void) {
  return tasm_resolve_deterministic;
}
PROOF thm get_tasm_resolve_sound(void) { return tasm_resolve_sound; }
PROOF thm get_tasm_data_fits_def(void) { return tasm_data_fits_def; }
PROOF thm get_tasm_denotes_object_wf(void) {
  return tasm_denotes_object_wf;
}
PROOF thm get_tasm_code_label_inversion(void) {
  return tasm_code_label_inversion;
}
PROOF thm get_tasm_word_inversion(void) { return tasm_word_inversion; }
PROOF thm get_tasm_patch_words_one(void) {
  return tasm_patch_words_one;
}
PROOF thm get_tasm_space_inversion(void) {
  return tasm_space_inversion;
}
PROOF thm get_tasm_space_emits_none(void) {
  return tasm_space_emits_none;
}
PROOF thm get_tasm_wrong_section_no_denotation(void) {
  return tasm_wrong_section_no_denotation;
}
PROOF thm get_tasm_example_resolution(void) {
  return tasm_example_resolution;
}

PROOF static int _tasm_model_audit(void) {
  thm_list pubs = THM_LIST(
      tasm_section_RECURSION, tasm_operand_RECURSION,
      tasm_item_RECURSION, tasm_binding_RECURSION,
      tasm_result_RECURSION, tasm_item_line_def, tasm_item_kind_def,
      tasm_item_section_def, tasm_item_label_def, tasm_item_opcode_def,
      tasm_item_operand_def, tasm_item_values_def, tasm_item_count_def,
      tasm_end_section_def, tasm_code_width_from_def,
      tasm_data_width_from_def, tasm_labels_def,
      tasm_label_denotes_def, tasm_items_wf_def, tasm_semantic_ok_def,
      tasm_code_image_def, tasm_data_patches_def, tasm_object_image_def,
      tasm_denotes_def, tasm_candidates_def, tasm_resolve_def,
      tasm_resolver_object_image_eq,
      tasm_resolve_deterministic, tasm_resolve_sound,
      tasm_data_fits_def, tasm_denotes_object_wf,
      tasm_code_label_inversion, tasm_word_inversion,
      tasm_patch_words_one, tasm_space_inversion,
      tasm_space_emits_none, tasm_wrong_section_no_denotation,
      tasm_example_resolution);
  for (size_t i = 0; i < vector_size(pubs); ++i) {
    ENSURE_COND(!IS_NULL(pubs[i]), "TASM theorem %zu is empty", i);
    ENSURE_COND(vector_size(hyp(pubs[i])) == 0,
                "TASM theorem %zu has hypotheses", i);
  }
  term object = tasm_example_object();
  term expected =
      `(tasm_resolve
          [TasmEntry 1i 0i;
           TasmLabel 2i 0i;
           TasmInstr 3i TVMPushOp (TasmDataRef 1i);
           TasmInstr 4i TVMLoadBOp TasmNoOperand;
           TasmInstr 5i TVMPutcOp TasmNoOperand;
           TasmInstr 6i TVMJmpOp (TasmCodeRef 2i);
           TasmSection 7i TasmData;
           TasmLabel 8i 1i;
           TasmByte 9i [65i];
           TasmSpace 10i 3i;
           TasmSection 11i TasmCode;
           TasmLabel 12i 2i;
           TasmInstr 13i TVMPushOp (TasmImm 0i);
           TasmInstr 14i TVMHaltOp TasmNoOperand] ==
         TasmOk (${object:tvm_object})) &&
        tvm_terminates (${object:tvm_object})
          ([]:(int)list) [65i] 0i`;
  ENSURE_COND(!IS_NULL(tasm_example_resolution) &&
      vector_size(hyp(tasm_example_resolution)) == 0 &&
      vector_size(free_vars(concl(tasm_example_resolution))) == 0 &&
      alpha_compare(concl(tasm_example_resolution), expected) == 0,
      "TASM execution example has the wrong contract");
  ENSURE_COND(alpha_compare(concl(tasm_denotes_def),
      `tasm_denotes (items:(tasm_item)list) (obj:tvm_object) <=>
       (tasm_items_wf items &&
        tasm_semantic_ok items &&
        obj == tasm_object_image items)`) == 0,
      "TASM declarative denotation has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tasm_resolve_def),
      `tasm_resolve (items:(tasm_item)list) ==
       (if tasm_candidates items == [] && tasm_semantic_ok items
        then TasmOk (tasm_resolver_object_image items)
        else TasmFail
          (tasm_error_line (tasm_selected_error items))
          (tasm_error_rank (tasm_selected_error items)))`) == 0,
      "TASM resolver has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tasm_resolver_object_image_eq),
      `!(items:(tasm_item)list).
         tasm_resolver_object_image items == tasm_object_image items`) == 0,
      "TASM resolver image bridge has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tasm_resolve_deterministic),
      `!items result1 result2.
         tasm_resolve (items:(tasm_item)list) ==
           (result1:tasm_result) ==>
         tasm_resolve items == (result2:tasm_result) ==>
         result1 == result2`) == 0,
      "TASM resolver determinism has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tasm_resolve_sound),
      `!items obj.
         tasm_items_wf (items:(tasm_item)list) &&
         tasm_resolve items == TasmOk (obj:tvm_object) ==>
         tasm_denotes items obj`) == 0,
      "TASM resolver soundness has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tasm_denotes_object_wf),
      `!items obj.
         tasm_denotes (items:(tasm_item)list) (obj:tvm_object) ==>
         tasm_data_fits items ==> tvm_object_wf obj`) == 0,
      "TASM object well-formedness bridge has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tasm_code_label_inversion),
      `!items obj label addr.
         tasm_denotes (items:(tasm_item)list) (obj:tvm_object) ==>
         tasm_label_denotes items (label:int) TasmCode (addr:int) ==>
         addr == tasm_label_address items label`) == 0,
      "TASM code-label inversion has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tasm_word_inversion),
      `!items line values patches.
         tasm_word_denotes (items:(tasm_item)list) (line:int)
           (values:(int)list) (patches:(tvm_patch)list) ==>
         ?before after.
           items == before ++ (TasmWord line values :: after) &&
           tasm_end_section TasmCode before == TasmData &&
           patches ==
             tasm_patch_words
               (8i + tasm_data_width_from TasmCode before) values`) == 0,
      "TASM word inversion has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tasm_patch_words_one),
      `!addr value.
         tasm_patch_words (addr:int) [(value:int)] ==
         tasm_patch_bytes addr (tower_word_bytes value)`) == 0,
      "TASM single-word patch theorem has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tasm_space_inversion),
      `!items line count before_addr after_addr.
         tasm_space_denotes (items:(tasm_item)list) (line:int)
           (count:int) (before_addr:int) (after_addr:int) ==>
         ?before after.
           items == before ++ (TasmSpace line count :: after) &&
           tasm_end_section TasmCode before == TasmData &&
           before_addr ==
             8i + tasm_data_width_from TasmCode before &&
           after_addr == before_addr + count`) == 0,
      "TASM space inversion has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tasm_space_emits_none),
      `!addr line count rest.
         tasm_data_patches_from TasmData (addr:int)
           (TasmSpace (line:int) (count:int) ::
             (rest:(tasm_item)list)) ==
         tasm_data_patches_from TasmData (addr + count) rest`) == 0,
      "TASM space inversion has the wrong conclusion");
  ENSURE_COND(alpha_compare(concl(tasm_wrong_section_no_denotation),
      `!items obj. tasm_wrong_section (items:(tasm_item)list) ==>
         ~(tasm_denotes items (obj:tvm_object))`) == 0,
      "TASM wrong-section inversion has the wrong conclusion");
  ENSURE_COND(vector_size(get_all_axioms()) == _tasm_axioms_before,
              "TASM model introduced an axiom");
  return 0;
err:
  ERR_FUN_PUTS("_tasm_model_audit");
  return -1;
}
PROOF int _tasm_model_audit_run = _tasm_model_audit();
