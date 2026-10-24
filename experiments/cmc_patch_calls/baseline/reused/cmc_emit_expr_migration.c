#include "cmc_layout_migration_abi.h"
struct cm_emitter { struct cm_output *output; int pc; };

/*@ Extern Coq
 (cm_type :: *)
 (cm_expr :: *)
 (cm_leaf_expr :: *)
 (cm_program :: *)
 (cm_function_d :: *)
 (cm_struct_d :: *)
 (cm_global_d :: *)
 (cm_string_d :: *)
 (cm_lookup_policy :: *)
 (cm_codegen_obligations :: *)
 (tvm_inst :: *)
 (tvm_opcode :: *)
 (cm_slot_d :: *)
 (cm_simple_view :: *)
 (bool :: *)
 (cm_stmt :: *)
 (cm_tpair :: *)
 (cm_apair :: *)
*/
/*@ Extern Coq
 (cm_type_encode : cm_type -> Z)
 (cm_typed_program : cm_lookup_policy -> cm_program -> Prop)
 (cm_program_structs : cm_program -> list cm_struct_d)
 (cm_program_globals : cm_program -> list cm_global_d)
 (cm_program_strings : cm_program -> list cm_string_d)
 (cm_program_functions : cm_program -> list cm_function_d)
 (cm_function_at : cm_lookup_policy -> Z -> list cm_function_d -> cm_function_d)
 (cm_rep_structs_safe : list cm_struct_d -> Prop)
 (cm_rep_globals_safe : list cm_global_d -> Prop)
 (cm_rep_strings_safe : list cm_string_d -> Prop)
 (cm_rep_globals_size : list cm_global_d -> Z)
 (cm_rep_strings_size : list cm_string_d -> Z)
 (cm_program_context_rep : Z -> cm_program -> Z -> Assertion)
 (cm_function_context_rep : Z -> cm_function_d -> Z -> Z -> Assertion)
 (cm_expr_rep : Z -> cm_expr -> Assertion)
 (cm_rep_expr_kind : cm_expr -> Z)
 (cm_rep_expr_op : cm_expr -> Z)
 (cm_rep_expr_value : cm_expr -> Z)
 (cm_expr_type : cm_expr -> cm_type)
 (cm_expr_payload : cm_expr -> Z -> Z -> Z -> Assertion)
 (cm_resolved_emitter_plan_rep : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> list tvm_inst -> list tvm_inst -> Assertion)
 (cm_wf_program : cm_lookup_policy -> cm_codegen_obligations -> cm_program -> Prop)
 (cm_expr_wf : cm_lookup_policy -> cm_program -> cm_function_d -> cm_expr -> Prop)
 (cm_expr_counts_representable : cm_lookup_policy -> cm_program -> Z -> cm_expr -> Prop)
 (cm_function_params : cm_function_d -> list cm_slot_d)
 (cm_function_locals : cm_function_d -> list cm_slot_d)
 (cm_slots_wf : list cm_struct_d -> list cm_slot_d -> Prop)
 (cm_rep_members_safe : list cm_slot_d -> Prop)
 (TVMInst : tvm_opcode -> Z -> tvm_inst)
 (cm_temp_store_code : cm_lookup_policy -> cm_program -> Z -> Z -> list tvm_inst)
 (cm_temp_load_code : cm_lookup_policy -> cm_program -> Z -> Z -> list tvm_inst)
 (cm_temp_offset : cm_lookup_policy -> cm_program -> Z -> Z -> Z)
 (TVMCallOp : tvm_opcode)
 (cm_function_pc : cm_lookup_policy -> cm_program -> Z -> Z)
 (cm_rvalue_code_count : cm_lookup_policy -> cm_program -> Z -> cm_expr -> Z)
 (cm_i32_code_count : Z -> Prop)
 (cm_rep_args_safe : list cm_expr -> Prop)
 (cm_rep_args_length : list cm_expr -> Z)
 (cm_arg_list_rep : Z -> list cm_expr -> Assertion)
 (cm_args_apair : list cm_expr -> cm_apair)
 (cm_adepth : cm_apair -> Z)
 (cm_args_head : list cm_expr -> cm_expr)
 (cm_args_tail : list cm_expr -> list cm_expr)
 (cm_call_slots_tail : list cm_slot_d -> list cm_slot_d)
 (cm_call_args : cm_expr -> list cm_expr)
 (CMCallE : Z -> list cm_expr -> cm_type -> cm_expr)
 (cm_emit_args_reload : cm_lookup_policy -> cm_program -> Z -> Z -> list cm_expr -> list tvm_inst)
 (cm_emit_args_store : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> Z -> list cm_expr -> list tvm_inst)
 (cm_expr_code_for : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> cm_expr -> Z -> list tvm_inst)
 (cm_expr_temps_for : cm_expr -> Z -> Z)
 (cm_args_wf : cm_lookup_policy -> cm_program -> cm_function_d -> list cm_expr -> list cm_slot_d -> Prop)
 (cm_args_counts_representable : cm_lookup_policy -> cm_program -> Z -> list cm_expr -> Prop)
 (cm_leaf_code_for : cm_program -> cm_leaf_expr -> Z -> list tvm_inst)
 (cm_type_code_wf : cm_type -> Prop)
 (cm_dispatch_leaf : cm_expr -> Prop)
 (cm_leaf_source_expr : cm_leaf_expr -> cm_expr)
 (cm_binding_valid : cm_program -> cm_function_d -> Z -> Z -> Prop)
 (CMVarE : Z -> Z -> cm_type -> cm_expr)
 (cm_var_code_for : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> cm_type -> Z -> list tvm_inst)
 (CMSimpleLeaf : cm_leaf_expr -> cm_simple_view)
 (CMSimpleVar : Z -> Z -> cm_type -> cm_simple_view)
 (cm_simple_expr : cm_expr -> Prop)
 (cm_simple_source_expr : cm_simple_view -> cm_expr)
 (cm_simple_code_for : cm_lookup_policy -> cm_program -> Z -> cm_simple_view -> Z -> list tvm_inst)
 (cm_type_refs : list cm_struct_d -> cm_type -> Prop)
 (cm_type_size : list cm_struct_d -> cm_type -> Z)
 (cm_is_pointer : cm_type -> Prop)
 (cm_pointee : cm_type -> cm_type)
 (cm_rep_is_pointer_code : Z -> Z)
 (cm_pointer_scale : cm_program -> cm_expr -> Z)
 (cm_binary_finish_code : cm_lookup_policy -> cm_program -> Z -> Z -> cm_expr -> cm_expr -> Z -> list tvm_inst)
 (cm_binary_opcode : Z -> tvm_opcode)
 (tvm_opcode_code : tvm_opcode -> Z)
 (TVMPushOp : tvm_opcode)
 (TVMSwapOp : tvm_opcode)
 (TVMAddOp : tvm_opcode)
 (TVMSubOp : tvm_opcode)
 (TVMMulOp : tvm_opcode)
 (TVMDivOp : tvm_opcode)
 (CMConstE : Z -> cm_type -> cm_expr)
 (CMStringE : Z -> cm_type -> cm_expr)
 (CMGetcE : cm_type -> cm_expr)
 (CMSizeofE : cm_type -> cm_type -> cm_expr)
 (CMLeafConst : Z -> cm_type -> cm_leaf_expr)
 (CMLeafString : Z -> cm_type -> cm_leaf_expr)
 (CMLeafGetc : cm_type -> cm_leaf_expr)
 (CMLeafSizeof : cm_type -> cm_type -> cm_leaf_expr)
 (cm_const_immediate : cm_type -> Z -> Z)
 (cm_string_address : cm_program -> Z -> Z)
 (cm_member_valid : cm_program -> cm_type -> Z -> Prop)
 (cm_member_array_code : cm_program -> cm_type -> Z -> Z)
 (cm_member_offset : list cm_struct_d -> Z -> Z -> Z)
 (cm_struct_id : cm_type -> Z)
 (cm_program_main : cm_program -> Z)
 (cm_rep_string_address : list cm_global_d -> list cm_string_d -> Z -> Z)
 (cm_rep_type_size : list cm_struct_d -> Z -> Z)
 (cm_rep_struct_member_prefix : list cm_struct_d -> Z -> Z -> Z)
 (cm_struct_list_rep : Z -> list cm_struct_d -> Assertion)
 (cm_global_list_rep : Z -> list cm_global_d -> Assertion)
 (cm_string_list_rep : Z -> list cm_string_d -> Assertion)
 (TVMGetcOp : tvm_opcode)
 (CMCharTy : cm_type)
 (cm_rep_ops : list tvm_inst -> list Z)
 (cm_rep_imms : list tvm_inst -> list Z)
 (cm_emitter_rep : Z -> Z -> Z -> list Z -> list Z -> Assertion)
 (cm_emitter_plan_rep : Z -> Z -> Z -> list tvm_inst -> list tvm_inst -> Assertion)
 (cm_char_normalize_code : cm_type -> list tvm_inst)
 (cm_load_code : cm_type -> list tvm_inst)
 (cm_store_code : cm_type -> list tvm_inst)
 (cm_fp_relative_address_code : Z -> list tvm_inst)
 (cm_function_ret : cm_function_d -> cm_type)
 (cm_rep_members_size : list cm_slot_d -> Z)
 (cm_slot_list_rep : Z -> list cm_slot_d -> Assertion)
 (TVMModOp : tvm_opcode)
 (TVMLoadOp : tvm_opcode)
 (TVMLoadBOp : tvm_opcode)
 (TVMStoreOp : tvm_opcode)
 (TVMStoreBOp : tvm_opcode)
 (cm_patch_code : cm_lookup_policy -> cm_program -> list tvm_inst -> list tvm_inst)
 (cm_resolved_emitter_rep : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> list tvm_inst -> Assertion)
 (cm_stmt_rep : Z -> cm_stmt -> Assertion)
 (cm_stmt_wf : cm_lookup_policy -> cm_program -> cm_function_d -> bool -> cm_stmt -> Prop)
 (cm_stmt_counts_representable : cm_lookup_policy -> cm_program -> Z -> cm_stmt -> Prop)
 (cm_lvalue_code_count : cm_lookup_policy -> cm_program -> Z -> cm_expr -> Z)
 (cm_stmt_code_count : cm_lookup_policy -> cm_program -> Z -> cm_stmt -> Z)
 (cm_expr_shape : cm_expr -> cm_expr -> Prop)
 (cm_intrinsic_expr : cm_expr -> Prop)
 (cm_expr_child : cm_expr -> cm_expr)
 (cm_expr_second : cm_expr -> cm_expr)
 (CMUnaryE : Z -> cm_expr -> cm_type -> cm_expr)
 (CMIndexE : cm_expr -> cm_expr -> cm_type -> cm_expr)
 (CMAssignE : cm_expr -> cm_expr -> cm_type -> cm_expr)
 (CMBinaryE : Z -> cm_expr -> cm_expr -> cm_type -> cm_expr)
 (CMMemberE : cm_expr -> Z -> cm_type -> cm_expr)
 (CMPutcE : cm_expr -> cm_type -> cm_expr)
 (CMPutiE : cm_expr -> cm_type -> cm_expr)
 (CMExitE : cm_expr -> cm_type -> cm_expr)
 (cm_optional_load : cm_type -> Z -> list tvm_inst)
 (cm_member_load_suffix : cm_program -> cm_expr -> Z -> cm_type -> Z -> list tvm_inst)
 (cm_short_opcode : Z -> tvm_opcode)
 (cm_short_value : Z -> Z)
 (TVMDupOp : tvm_opcode)
 (TVMPutcOp : tvm_opcode)
 (TVMPutiOp : tvm_opcode)
 (TVMHaltOp : tvm_opcode)
 (TVMEqOp : tvm_opcode)
 (TVMNeOp : tvm_opcode)
 (TVMJnzOp : tvm_opcode)
 (TVMJzOp : tvm_opcode)
 (TVMJmpOp : tvm_opcode)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_emit_expr_migration_lib */

void cm_emit_binary_finish_plan(struct cm_program *program, int fid,
                                struct cm_function *fn, int temp, int op,
                                struct cm_expr *left,
                                struct cm_expr *right,
                                struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (body : Z) (next : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (left_e : cm_expr) (right_e : cm_expr) (functions_ptr : Z)
 Require cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && 0 <= temp && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_rep_structs_safe(cm_program_structs(p)) && cm_type_code_wf(cm_expr_type(left_e)) && cm_type_refs(cm_program_structs(p), cm_expr_type(left_e)) && cm_i32_code_count(cm_type_encode(cm_expr_type(left_e))) && cm_type_code_wf(cm_expr_type(right_e)) && cm_type_refs(cm_program_structs(p), cm_expr_type(right_e)) && cm_i32_code_count(cm_type_encode(cm_expr_type(right_e))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(left, left_e) * cm_expr_rep(right, right_e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_binary_finish_code(policy, p, fid, op, left_e, right_e, temp), tail))
 Ensure cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && 0 <= temp && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_rep_structs_safe(cm_program_structs(p)) && cm_type_code_wf(cm_expr_type(left_e)) && cm_type_refs(cm_program_structs(p), cm_expr_type(left_e)) && cm_i32_code_count(cm_type_encode(cm_expr_type(left_e))) && cm_type_code_wf(cm_expr_type(right_e)) && cm_type_refs(cm_program_structs(p), cm_expr_type(right_e)) && cm_i32_code_count(cm_type_encode(cm_expr_type(right_e))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(left, left_e) * cm_expr_rep(right, right_e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_binary_finish_code(policy, p, fid, op, left_e, right_e, temp)), tail)
*/;

void cm_emit_call_expr(struct cm_program *program, int fid,
                       struct cm_function *fn, int pc, int temp,
                       int temp_limit, struct cm_expr *expr,
                       int lvalue, struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require cm_rep_expr_kind(e) == 8 && 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
 Ensure cm_rep_expr_kind(e) == 8 && 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue)), tail)
*/;

void cm_emit_load_plan(struct cm_emitter *emitter, int ty)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (model_ty : cm_type)
    Require ty == cm_type_encode(model_ty) && cm_type_code_wf(model_ty) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_load_code(model_ty), tail))
    Ensure cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_load_code(model_ty)), tail)
*/;

void cm_emit_normalize_plan(struct cm_emitter *emitter, int ty)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (model_ty : cm_type)
    Require ty == cm_type_encode(model_ty) && cm_type_code_wf(model_ty) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_char_normalize_code(model_ty), tail))
    Ensure cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_char_normalize_code(model_ty)), tail)
*/;

void cm_emit_plan(struct cm_emitter *emitter, int op,
                  long long immediate)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (opcode : tvm_opcode)
    Require op == tvm_opcode_code(opcode) && tvm_opcode_code(opcode) != 22 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, cons(TVMInst(opcode, immediate), tail))
    Ensure cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cons(TVMInst(opcode, immediate), nil)), tail)
*/;

void cm_emit_simple_expr(struct cm_program *program, int fid,
                         struct cm_function *fn, int pc, int temp,
                         struct cm_expr *expr, int lvalue,
                         struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (simple : cm_simple_view)
 (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require 0 <= lvalue && lvalue <= 1 && e == cm_simple_source_expr(simple) && cm_simple_expr(e) &&
 cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_simple_code_for(policy, p, fid, simple, lvalue), tail))
 Ensure 0 <= lvalue && lvalue <= 1 && e == cm_simple_source_expr(simple) && cm_simple_expr(e) &&
 cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_simple_code_for(policy, p, fid, simple, lvalue)), tail)
*/;

void cm_emit_store_plan(struct cm_emitter *emitter, int ty)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (model_ty : cm_type)
    Require ty == cm_type_encode(model_ty) && cm_type_code_wf(model_ty) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_store_code(model_ty), tail))
    Ensure cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_store_code(model_ty)), tail)
*/;

void cm_emit_temp_load_plan(struct cm_function *fn, int temp,
                            struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (f : cm_function_d) (fid : Z) (structs : list cm_struct_d) (body : Z) (next : Z)
    Require 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_temp_load_code(policy, p, fid, temp), tail))
    Ensure 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_temp_load_code(policy, p, fid, temp)), tail)
*/;

void cm_emit_temp_store_plan(struct cm_function *fn, int temp,
                             struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (f : cm_function_d) (fid : Z) (structs : list cm_struct_d) (body : Z) (next : Z)
    Require 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_temp_store_code(policy, p, fid, temp), tail))
    Ensure 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_temp_store_code(policy, p, fid, temp)), tail)
*/;

int cm_expr_lvalue_count_context(struct cm_program *program, int fid,
                                 struct cm_function *fn,
                                 struct cm_expr *expr)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (body : Z) (next : Z) (functions_ptr : Z)
    Require cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e)
    Ensure cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_lvalue_code_count(policy, p, fid, e) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e)
*/;

int cm_expr_rvalue_count_context(struct cm_program *program, int fid,
                                 struct cm_function *fn,
                                 struct cm_expr *expr)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (body : Z) (next : Z) (functions_ptr : Z)
    Require cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e)
    Ensure cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_rvalue_code_count(policy, p, fid, e) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e)
*/;

void cm_expr_type_code_context(struct cm_expr *expr, int *code)
/*@ With (e : cm_expr)
    Require cm_expr_rep(expr, e) * undef_data_at(code, int)
    Ensure cm_expr_rep(expr, e) * data_at(code, int, cm_type_encode(cm_expr_type(e)))
*/;

int cm_member_array_value_context(struct cm_program *program,
                                  int base_ty, int mid)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (base : cm_type) (functions_ptr : Z)
 Require base_ty == cm_type_encode(base) && cm_i32_code_count(base_ty) && cm_typed_program(policy, p) && cm_type_code_wf(base) && cm_member_valid(p, base, mid) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr)
 Ensure base_ty == cm_type_encode(base) && cm_i32_code_count(base_ty) && cm_typed_program(policy, p) && cm_type_code_wf(base) && cm_member_valid(p, base, mid) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_member_array_code(p, base, mid) && cm_program_context_rep(program, p, functions_ptr)
*/;

long long cm_member_offset_value_context(struct cm_program *program,
                                         int base_ty, int mid)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (base : cm_type) (functions_ptr : Z)
 Require base_ty == cm_type_encode(base) && cm_i32_code_count(base_ty) && cm_typed_program(policy, p) && cm_type_code_wf(base) && cm_member_valid(p, base, mid) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr)
 Ensure base_ty == cm_type_encode(base) && cm_i32_code_count(base_ty) && cm_typed_program(policy, p) && cm_type_code_wf(base) && cm_member_valid(p, base, mid) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_member_offset(cm_program_structs(p), cm_struct_id(cm_pointee(base)), mid) && cm_program_context_rep(program, p, functions_ptr)
*/;

long long cm_type_size_value(struct cm_program *program,
                             long long code)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (asked : cm_type) (functions_ptr : Z)
 Require code == cm_type_encode(asked) && cm_typed_program(policy, p) && cm_type_code_wf(asked) && cm_type_refs(cm_program_structs(p), asked) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr)
 Ensure code == cm_type_encode(asked) && cm_typed_program(policy, p) && cm_type_code_wf(asked) && cm_type_refs(cm_program_structs(p), asked) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_type_size(cm_program_structs(p), asked) && cm_program_context_rep(program, p, functions_ptr)
*/;

void cm_emit_expr(struct cm_program *program, int fid,
                  struct cm_function *fn, int pc, int temp,
                  int temp_limit, struct cm_expr *expr, int lvalue,
                  struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
 Ensure 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue)), tail)
*/;

static void cm_emit_intrinsic_expr(struct cm_program *program, int fid,
                            struct cm_function *fn, int pc, int temp,
                            int temp_limit, struct cm_expr *expr,
                            int lvalue, struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require cm_intrinsic_expr(e) && 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
 Ensure cm_intrinsic_expr(e) && 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue)), tail)
*/
{
  /*@ cm_intrinsic_expr(e) && cm_expr_rep(expr, e)
      which implies exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && cm_intrinsic_expr(e) && xa != 0 && xb == 0 && xargs == 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_rep(xa, cm_expr_child(e)) */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && 0 <= temp_limit && temp_limit <= 2147483647 && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_type_code_wf(cm_expr_type(e)) && cm_type_refs(cm_program_structs(p), cm_expr_type(e)) && cm_expr_wf(policy, p, f, cm_expr_child(e)) && cm_expr_counts_representable(policy, p, fid, cm_expr_child(e)) && cm_type_code_wf(cm_expr_type(cm_expr_child(e))) && cm_type_refs(cm_program_structs(p), cm_expr_type(cm_expr_child(e))) && cm_i32_code_count(cm_type_encode(cm_expr_type(cm_expr_child(e)))) && emp */
  

  if (expr->kind == CMC_EXPR_PUTC) {
    if (!lvalue) {
      
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && cm_rep_expr_kind(e) == 11 && 0 <= lvalue && lvalue <= 0 && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && cm_rep_expr_kind(e) == 11 && 0 <= lvalue && lvalue <= 0 && cm_expr_shape(e, CMPutcE(cm_expr_child(e), cm_expr_type(e))) && emp */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && cm_rep_expr_kind(e) == 11 && 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && cm_rep_expr_kind(e) == 11 && 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, cm_expr_child(e), 0), cons(TVMInst(TVMDupOp, 0), cons(TVMInst(TVMPutcOp, 0), tail)))) */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && cm_rep_expr_kind(e) == 11 && 0 <= lvalue && lvalue <= 0 && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && cm_rep_expr_kind(e) == 11 && 0 <= lvalue && lvalue <= 0 && 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(cm_expr_child(e), 0) <= temp_limit && cm_i32_code_count(pc) && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, cm_expr_child(e), 0))) && emp */
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = cm_expr_child(e), body = body, next = next, functions_ptr = functions_ptr, done = done, tail = cons(TVMInst(TVMDupOp, 0), cons(TVMInst(TVMPutcOp, 0), tail)), out = out, capacity = capacity */;
      cm_emit_plan(emitter, CMC_OP_DUP, 0) /*@ where policy = policy, p = p, done = app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_expr_child(e), 0)), tail = cons(TVMInst(TVMPutcOp, 0), tail), out = out, capacity = capacity, opcode = TVMDupOp */;
      cm_emit_plan(emitter, CMC_OP_PUTC, 0) /*@ where policy = policy, p = p, done = app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_expr_child(e), 0)), cons(TVMInst(TVMDupOp, 0), nil)), tail = tail, out = out, capacity = capacity, opcode = TVMPutcOp */;
    } else {
    }
  } else if (expr->kind == CMC_EXPR_PUTI) {
    if (!lvalue) {
      
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && cm_rep_expr_kind(e) == 12 && 0 <= lvalue && lvalue <= 0 && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && cm_rep_expr_kind(e) == 12 && 0 <= lvalue && lvalue <= 0 && cm_expr_shape(e, CMPutiE(cm_expr_child(e), cm_expr_type(e))) && emp */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && cm_rep_expr_kind(e) == 12 && 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && cm_rep_expr_kind(e) == 12 && 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, cm_expr_child(e), 0), cons(TVMInst(TVMDupOp, 0), cons(TVMInst(TVMPutiOp, 0), tail)))) */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && cm_rep_expr_kind(e) == 12 && 0 <= lvalue && lvalue <= 0 && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && cm_rep_expr_kind(e) == 12 && 0 <= lvalue && lvalue <= 0 && 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(cm_expr_child(e), 0) <= temp_limit && cm_i32_code_count(pc) && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, cm_expr_child(e), 0))) && emp */
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = cm_expr_child(e), body = body, next = next, functions_ptr = functions_ptr, done = done, tail = cons(TVMInst(TVMDupOp, 0), cons(TVMInst(TVMPutiOp, 0), tail)), out = out, capacity = capacity */;
      cm_emit_plan(emitter, CMC_OP_DUP, 0) /*@ where policy = policy, p = p, done = app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_expr_child(e), 0)), tail = cons(TVMInst(TVMPutiOp, 0), tail), out = out, capacity = capacity, opcode = TVMDupOp */;
      cm_emit_plan(emitter, CMC_OP_PUTI, 0) /*@ where policy = policy, p = p, done = app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_expr_child(e), 0)), cons(TVMInst(TVMDupOp, 0), nil)), tail = tail, out = out, capacity = capacity, opcode = TVMPutiOp */;
    } else {
    }
  } else {
    if (!lvalue) {
      
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && cm_rep_expr_kind(e) != 11 && cm_rep_expr_kind(e) != 12 && 0 <= lvalue && lvalue <= 0 && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && cm_rep_expr_kind(e) != 11 && cm_rep_expr_kind(e) != 12 && 0 <= lvalue && lvalue <= 0 && cm_expr_shape(e, CMExitE(cm_expr_child(e), cm_expr_type(e))) && emp */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && cm_rep_expr_kind(e) != 11 && cm_rep_expr_kind(e) != 12 && 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && cm_rep_expr_kind(e) != 11 && cm_rep_expr_kind(e) != 12 && 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, cm_expr_child(e), 0), app(cm_char_normalize_code(CMCharTy), cons(TVMInst(TVMHaltOp, 0), tail)))) */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && cm_rep_expr_kind(e) != 11 && cm_rep_expr_kind(e) != 12 && 0 <= lvalue && lvalue <= 0 && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_intrinsic_expr(e) && cm_rep_expr_kind(e) != 11 && cm_rep_expr_kind(e) != 12 && 0 <= lvalue && lvalue <= 0 && 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(cm_expr_child(e), 0) <= temp_limit && cm_i32_code_count(pc) && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, cm_expr_child(e), 0))) && emp */
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = cm_expr_child(e), body = body, next = next, functions_ptr = functions_ptr, done = done, tail = app(cm_char_normalize_code(CMCharTy), cons(TVMInst(TVMHaltOp, 0), tail)), out = out, capacity = capacity */;
      cm_emit_normalize_plan(emitter, CMC_TYPE_CHAR) /*@ where policy = policy, p = p, done = app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_expr_child(e), 0)), tail = cons(TVMInst(TVMHaltOp, 0), tail), out = out, capacity = capacity, model_ty = CMCharTy */;
      cm_emit_plan(emitter, CMC_OP_HALT, 0) /*@ where policy = policy, p = p, done = app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_expr_child(e), 0)), cm_char_normalize_code(CMCharTy)), tail = tail, out = out, capacity = capacity, opcode = TVMHaltOp */;
    } else {
    }
  }

  
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && cm_intrinsic_expr(e) && xa != 0 && xb == 0 && xargs == 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_rep(xa, cm_expr_child(e))
      which implies cm_expr_rep(expr, e) */
}



static void cm_emit_unary_expr(struct cm_program *program, int fid,
                               struct cm_function *fn, int pc, int temp,
                               int temp_limit, struct cm_expr *expr,
                               int lvalue, struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (op_ : Z) (arg_ : cm_expr) (ty_ : cm_type) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require e == CMUnaryE(op_, arg_, ty_) && 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
 Ensure e == CMUnaryE(op_, arg_, ty_) && 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue)), tail)
*/
{
  /*@ cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && cm_expr_rep(expr, e)
      which implies exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && xa != 0 && xb == 0 && xargs == 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, op_) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_rep(xa, arg_) */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && 0 <= temp_limit && temp_limit <= 2147483647 && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_type_code_wf(cm_expr_type(e)) && cm_type_refs(cm_program_structs(p), cm_expr_type(e)) && cm_expr_wf(policy, p, f, arg_) && cm_expr_counts_representable(policy, p, fid, arg_) && cm_type_code_wf(cm_expr_type(arg_)) && cm_type_refs(cm_program_structs(p), cm_expr_type(arg_)) && cm_i32_code_count(cm_type_encode(cm_expr_type(arg_))) && cm_expr_type(e) == ty_ && cm_type_code_wf(ty_) && cm_type_refs(cm_program_structs(p), ty_) && cm_rep_expr_op(e) == op_ && emp */
  

  if (expr->op == CMC_UN_DEREF) {
    if (!lvalue) {
      
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ == 2 && 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ == 2 && 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0), app(cm_load_code(ty_), tail))) */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ == 2 && 0 <= lvalue && lvalue <= 0 && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ == 2 && 0 <= lvalue && lvalue <= 0 && 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(arg_, 0) <= temp_limit && cm_i32_code_count(pc) && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0))) && emp */
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = arg_, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = app(cm_load_code(ty_), tail), out = out, capacity = capacity */;
      cm_emit_load_plan(emitter, expr->ty) /*@ where policy = policy, p = p, done = app(done, cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0)), tail = tail, out = out, capacity = capacity, model_ty = ty_ */;
    } else {
      
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ == 2 && lvalue != 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ == 2 && lvalue != 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0), tail)) */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ == 2 && lvalue != 0 && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ == 2 && lvalue != 0 && 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(arg_, 0) <= temp_limit && cm_i32_code_count(pc) && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0))) && emp */
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = arg_, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity */;
    }
  } else if (expr->op == CMC_UN_ADDR) {
    if (!lvalue) {
      
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ == 3 && 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ == 3 && 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, arg_, 1), tail)) */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ == 3 && 0 <= lvalue && lvalue <= 0 && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ == 3 && 0 <= lvalue && lvalue <= 0 && 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(arg_, 1) <= temp_limit && cm_i32_code_count(pc) && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, arg_, 1))) && emp */
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 1, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = arg_, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity */;
    } else {
    }
  } else {
    if (!lvalue) {
      if (expr->op == CMC_UN_NEG) {
        
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ != 2 && op_ != 3 && op_ == 0 && 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ != 2 && op_ != 3 && op_ == 0 && 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0), cons(TVMInst(TVMPushOp, -1), cons(TVMInst(TVMMulOp, 0), tail)))) */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ != 2 && op_ != 3 && op_ == 0 && 0 <= lvalue && lvalue <= 0 && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ != 2 && op_ != 3 && op_ == 0 && 0 <= lvalue && lvalue <= 0 && 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(arg_, 0) <= temp_limit && cm_i32_code_count(pc) && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0))) && emp */
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                     expr->a, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = arg_, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = cons(TVMInst(TVMPushOp, -1), cons(TVMInst(TVMMulOp, 0), tail)), out = out, capacity = capacity */;
        cm_emit_plan(emitter, CMC_OP_PUSH, -1) /*@ where policy = policy, p = p, done = app(done, cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0)), tail = cons(TVMInst(TVMMulOp, 0), tail), out = out, capacity = capacity, opcode = TVMPushOp */;
        cm_emit_plan(emitter, CMC_OP_MUL, 0) /*@ where policy = policy, p = p, done = app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0)), cons(TVMInst(TVMPushOp, -1), nil)), tail = tail, out = out, capacity = capacity, opcode = TVMMulOp */;
      } else {
        
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ != 2 && op_ != 3 && op_ != 0 && 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ != 2 && op_ != 3 && op_ != 0 && 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0), cons(TVMInst(TVMPushOp, 0), cons(TVMInst(TVMEqOp, 0), tail)))) */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ != 2 && op_ != 3 && op_ != 0 && 0 <= lvalue && lvalue <= 0 && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && op_ != 2 && op_ != 3 && op_ != 0 && 0 <= lvalue && lvalue <= 0 && 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(arg_, 0) <= temp_limit && cm_i32_code_count(pc) && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0))) && emp */
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                     expr->a, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = arg_, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = cons(TVMInst(TVMPushOp, 0), cons(TVMInst(TVMEqOp, 0), tail)), out = out, capacity = capacity */;
        cm_emit_plan(emitter, CMC_OP_PUSH, 0) /*@ where policy = policy, p = p, done = app(done, cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0)), tail = cons(TVMInst(TVMEqOp, 0), tail), out = out, capacity = capacity, opcode = TVMPushOp */;
        cm_emit_plan(emitter, CMC_OP_EQ, 0) /*@ where policy = policy, p = p, done = app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0)), cons(TVMInst(TVMPushOp, 0), nil)), tail = tail, out = out, capacity = capacity, opcode = TVMEqOp */;
      }
    } else {
    }
  }

  
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && cm_expr_shape(e, CMUnaryE(op_, arg_, ty_)) && xa != 0 && xb == 0 && xargs == 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, op_) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_rep(xa, arg_)
      which implies cm_expr_rep(expr, e) */
}



static void cm_emit_index_expr(struct cm_program *program, int fid,
                               struct cm_function *fn, int pc, int temp,
                               int temp_limit, struct cm_expr *expr,
                               int lvalue, struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (left_ : cm_expr) (right_ : cm_expr) (ty_ : cm_type) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require e == CMIndexE(left_, right_, ty_) && 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
 Ensure e == CMIndexE(left_, right_, ty_) && 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue)), tail)
*/
{
  /*@ cm_expr_shape(e, CMIndexE(left_, right_, ty_)) && cm_expr_rep(expr, e)
      which implies exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && cm_expr_shape(e, CMIndexE(left_, right_, ty_)) && xargs == 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_rep(xa, left_) * cm_expr_rep(xb, right_) */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMIndexE(left_, right_, ty_)) && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMIndexE(left_, right_, ty_)) && 0 <= temp_limit && temp_limit <= 2147483647 && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_type_code_wf(cm_expr_type(e)) && cm_type_refs(cm_program_structs(p), cm_expr_type(e)) && cm_expr_wf(policy, p, f, left_) && cm_expr_counts_representable(policy, p, fid, left_) && cm_type_code_wf(cm_expr_type(left_)) && cm_type_refs(cm_program_structs(p), cm_expr_type(left_)) && cm_i32_code_count(cm_type_encode(cm_expr_type(left_))) && cm_expr_wf(policy, p, f, right_) && cm_expr_counts_representable(policy, p, fid, right_) && cm_type_code_wf(cm_expr_type(right_)) && cm_type_refs(cm_program_structs(p), cm_expr_type(right_)) && cm_i32_code_count(cm_type_encode(cm_expr_type(right_))) && cm_expr_type(e) == ty_ && cm_type_code_wf(ty_) && cm_type_refs(cm_program_structs(p), ty_) && emp */
  

  int base_count = cm_expr_rvalue_count_context(
      program, fid, fn, expr->a) /*@ where policy = policy, cg = cg, p = p, f = f, e = left_, body = body, next = next, functions_ptr = functions_ptr */;
  long long element_size = cm_type_size_value(program, expr->ty) /*@ where policy = policy, p = p, asked = ty_, functions_ptr = functions_ptr */;
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMIndexE(left_, right_, ty_)) && base_count == cm_rvalue_code_count(policy, p, fid, left_) && element_size == cm_type_size(cm_program_structs(p), ty_) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMIndexE(left_, right_, ty_)) && base_count == cm_rvalue_code_count(policy, p, fid, left_) && element_size == cm_type_size(cm_program_structs(p), ty_) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, left_, 0), app(cm_temp_store_code(policy, p, fid, temp), app(cm_expr_code_for(policy, p, fid, pc + (base_count + 5), temp + 1, right_, 0), cons(TVMInst(TVMPushOp, element_size), cons(TVMInst(TVMMulOp, 0), app(cm_temp_load_code(policy, p, fid, temp), cons(TVMInst(TVMAddOp, 0), app(cm_optional_load(ty_, lvalue), tail))))))))) */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMIndexE(left_, right_, ty_)) && base_count == cm_rvalue_code_count(policy, p, fid, left_) && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMIndexE(left_, right_, ty_)) && base_count == cm_rvalue_code_count(policy, p, fid, left_) && 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(left_, 0) <= temp_limit && cm_i32_code_count(pc) && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, left_, 0))) && emp */
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
               expr->a, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = left_, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = app(cm_temp_store_code(policy, p, fid, temp), app(cm_expr_code_for(policy, p, fid, pc + (base_count + 5), temp + 1, right_, 0), cons(TVMInst(TVMPushOp, element_size), cons(TVMInst(TVMMulOp, 0), app(cm_temp_load_code(policy, p, fid, temp), cons(TVMInst(TVMAddOp, 0), app(cm_optional_load(ty_, lvalue), tail))))))), out = out, capacity = capacity */;
  cm_emit_temp_store_plan(fn, temp, emitter) /*@ where policy = policy, p = p, done = app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), tail = app(cm_expr_code_for(policy, p, fid, pc + (base_count + 5), temp + 1, right_, 0), cons(TVMInst(TVMPushOp, element_size), cons(TVMInst(TVMMulOp, 0), app(cm_temp_load_code(policy, p, fid, temp), cons(TVMInst(TVMAddOp, 0), app(cm_optional_load(ty_, lvalue), tail)))))), out = out, capacity = capacity, f = f, fid = fid, structs = cm_program_structs(p), body = body, next = next */;
  int right_pc = pc + (base_count + 5);
  int right_temp = temp + 1;
  struct cm_expr *right_expr = expr->b;
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMIndexE(left_, right_, ty_)) && base_count == cm_rvalue_code_count(policy, p, fid, left_) && right_pc == pc + (base_count + 5) && right_temp == temp + 1 && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMIndexE(left_, right_, ty_)) && base_count == cm_rvalue_code_count(policy, p, fid, left_) && right_pc == pc + (base_count + 5) && right_temp == temp + 1 && 0 <= right_temp && right_temp <= temp_limit && right_temp + cm_expr_temps_for(right_, 0) <= temp_limit && cm_i32_code_count(right_pc) && cm_i32_code_count(right_pc + Zlength(cm_expr_code_for(policy, p, fid, right_pc, right_temp, right_, 0))) && emp */
  cm_emit_expr(program, fid, fn, right_pc, right_temp, temp_limit,
               right_expr, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = right_, body = body, next = next, functions_ptr = functions_ptr, done = app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), cm_temp_store_code(policy, p, fid, temp)), tail = cons(TVMInst(TVMPushOp, element_size), cons(TVMInst(TVMMulOp, 0), app(cm_temp_load_code(policy, p, fid, temp), cons(TVMInst(TVMAddOp, 0), app(cm_optional_load(ty_, lvalue), tail))))), out = out, capacity = capacity */;
  cm_emit_plan(emitter, CMC_OP_PUSH, element_size) /*@ where policy = policy, p = p, done = app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), cm_temp_store_code(policy, p, fid, temp)), cm_expr_code_for(policy, p, fid, pc + (base_count + 5), temp + 1, right_, 0)), tail = cons(TVMInst(TVMMulOp, 0), app(cm_temp_load_code(policy, p, fid, temp), cons(TVMInst(TVMAddOp, 0), app(cm_optional_load(ty_, lvalue), tail)))), out = out, capacity = capacity, opcode = TVMPushOp */;
  cm_emit_plan(emitter, CMC_OP_MUL, 0) /*@ where policy = policy, p = p, done = app(app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), cm_temp_store_code(policy, p, fid, temp)), cm_expr_code_for(policy, p, fid, pc + (base_count + 5), temp + 1, right_, 0)), cons(TVMInst(TVMPushOp, element_size), nil)), tail = app(cm_temp_load_code(policy, p, fid, temp), cons(TVMInst(TVMAddOp, 0), app(cm_optional_load(ty_, lvalue), tail))), out = out, capacity = capacity, opcode = TVMMulOp */;
  cm_emit_temp_load_plan(fn, temp, emitter) /*@ where policy = policy, p = p, done = app(app(app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), cm_temp_store_code(policy, p, fid, temp)), cm_expr_code_for(policy, p, fid, pc + (base_count + 5), temp + 1, right_, 0)), cons(TVMInst(TVMPushOp, element_size), nil)), cons(TVMInst(TVMMulOp, 0), nil)), tail = cons(TVMInst(TVMAddOp, 0), app(cm_optional_load(ty_, lvalue), tail)), out = out, capacity = capacity, f = f, fid = fid, structs = cm_program_structs(p), body = body, next = next */;
  cm_emit_plan(emitter, CMC_OP_ADD, 0) /*@ where policy = policy, p = p, done = app(app(app(app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), cm_temp_store_code(policy, p, fid, temp)), cm_expr_code_for(policy, p, fid, pc + (base_count + 5), temp + 1, right_, 0)), cons(TVMInst(TVMPushOp, element_size), nil)), cons(TVMInst(TVMMulOp, 0), nil)), cm_temp_load_code(policy, p, fid, temp)), tail = app(cm_optional_load(ty_, lvalue), tail), out = out, capacity = capacity, opcode = TVMAddOp */;
  if (!lvalue) {
    
  /*@ 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(app(app(app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), cm_temp_store_code(policy, p, fid, temp)), cm_expr_code_for(policy, p, fid, pc + (base_count + 5), temp + 1, right_, 0)), cons(TVMInst(TVMPushOp, element_size), nil)), cons(TVMInst(TVMMulOp, 0), nil)), cm_temp_load_code(policy, p, fid, temp)), cons(TVMInst(TVMAddOp, 0), nil)), app(cm_optional_load(ty_, lvalue), tail))
      which implies 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(app(app(app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), cm_temp_store_code(policy, p, fid, temp)), cm_expr_code_for(policy, p, fid, pc + (base_count + 5), temp + 1, right_, 0)), cons(TVMInst(TVMPushOp, element_size), nil)), cons(TVMInst(TVMMulOp, 0), nil)), cm_temp_load_code(policy, p, fid, temp)), cons(TVMInst(TVMAddOp, 0), nil)), app(cm_load_code(ty_), tail)) */
  cm_emit_load_plan(emitter, expr->ty) /*@ where policy = policy, p = p, done = app(app(app(app(app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), cm_temp_store_code(policy, p, fid, temp)), cm_expr_code_for(policy, p, fid, pc + (base_count + 5), temp + 1, right_, 0)), cons(TVMInst(TVMPushOp, element_size), nil)), cons(TVMInst(TVMMulOp, 0), nil)), cm_temp_load_code(policy, p, fid, temp)), cons(TVMInst(TVMAddOp, 0), nil)), tail = tail, out = out, capacity = capacity, model_ty = ty_ */;
  } else {
  }

  
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && cm_expr_shape(e, CMIndexE(left_, right_, ty_)) && xargs == 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_rep(xa, left_) * cm_expr_rep(xb, right_)
      which implies cm_expr_rep(expr, e) */
}



static void cm_emit_assignment_expr(struct cm_program *program, int fid,
                                    struct cm_function *fn, int pc, int temp,
                                    int temp_limit, struct cm_expr *expr,
                                    int lvalue, struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (left_ : cm_expr) (right_ : cm_expr) (ty_ : cm_type) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require e == CMAssignE(left_, right_, ty_) && 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
 Ensure e == CMAssignE(left_, right_, ty_) && 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue)), tail)
*/
{
  /*@ cm_expr_shape(e, CMAssignE(left_, right_, ty_)) && cm_expr_rep(expr, e)
      which implies exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && cm_expr_shape(e, CMAssignE(left_, right_, ty_)) && xargs == 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_rep(xa, left_) * cm_expr_rep(xb, right_) */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMAssignE(left_, right_, ty_)) && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMAssignE(left_, right_, ty_)) && 0 <= temp_limit && temp_limit <= 2147483647 && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_type_code_wf(cm_expr_type(e)) && cm_type_refs(cm_program_structs(p), cm_expr_type(e)) && cm_expr_wf(policy, p, f, left_) && cm_expr_counts_representable(policy, p, fid, left_) && cm_type_code_wf(cm_expr_type(left_)) && cm_type_refs(cm_program_structs(p), cm_expr_type(left_)) && cm_i32_code_count(cm_type_encode(cm_expr_type(left_))) && cm_expr_wf(policy, p, f, right_) && cm_expr_counts_representable(policy, p, fid, right_) && cm_type_code_wf(cm_expr_type(right_)) && cm_type_refs(cm_program_structs(p), cm_expr_type(right_)) && cm_i32_code_count(cm_type_encode(cm_expr_type(right_))) && cm_expr_type(e) == ty_ && cm_type_code_wf(ty_) && cm_type_refs(cm_program_structs(p), ty_) && emp */
  

  if (!lvalue) {
    int left_count = cm_expr_lvalue_count_context(
        program, fid, fn, expr->a) /*@ where policy = policy, cg = cg, p = p, f = f, e = left_, body = body, next = next, functions_ptr = functions_ptr */;
    
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMAssignE(left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && left_count == cm_lvalue_code_count(policy, p, fid, left_) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMAssignE(left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && left_count == cm_lvalue_code_count(policy, p, fid, left_) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, left_, 1), app(cm_temp_store_code(policy, p, fid, temp), app(cm_expr_code_for(policy, p, fid, pc + (left_count + 5), temp + 1, right_, 0), app(cm_char_normalize_code(ty_), app(cm_temp_load_code(policy, p, fid, temp), app(cm_store_code(ty_), app(cm_temp_load_code(policy, p, fid, temp), app(cm_load_code(ty_), tail))))))))) */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMAssignE(left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && left_count == cm_lvalue_code_count(policy, p, fid, left_) && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMAssignE(left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && left_count == cm_lvalue_code_count(policy, p, fid, left_) && 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(left_, 1) <= temp_limit && cm_i32_code_count(pc) && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, left_, 1))) && emp */
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                 expr->a, 1, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = left_, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = app(cm_temp_store_code(policy, p, fid, temp), app(cm_expr_code_for(policy, p, fid, pc + (left_count + 5), temp + 1, right_, 0), app(cm_char_normalize_code(ty_), app(cm_temp_load_code(policy, p, fid, temp), app(cm_store_code(ty_), app(cm_temp_load_code(policy, p, fid, temp), app(cm_load_code(ty_), tail))))))), out = out, capacity = capacity */;
    cm_emit_temp_store_plan(fn, temp, emitter) /*@ where policy = policy, p = p, done = app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 1)), tail = app(cm_expr_code_for(policy, p, fid, pc + (left_count + 5), temp + 1, right_, 0), app(cm_char_normalize_code(ty_), app(cm_temp_load_code(policy, p, fid, temp), app(cm_store_code(ty_), app(cm_temp_load_code(policy, p, fid, temp), app(cm_load_code(ty_), tail)))))), out = out, capacity = capacity, f = f, fid = fid, structs = cm_program_structs(p), body = body, next = next */;
    int right_pc = pc + (left_count + 5);
    int right_temp = temp + 1;
    struct cm_expr *right_expr = expr->b;
    
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMAssignE(left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && left_count == cm_lvalue_code_count(policy, p, fid, left_) && right_pc == pc + (left_count + 5) && right_temp == temp + 1 && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMAssignE(left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && left_count == cm_lvalue_code_count(policy, p, fid, left_) && right_pc == pc + (left_count + 5) && right_temp == temp + 1 && 0 <= right_temp && right_temp <= temp_limit && right_temp + cm_expr_temps_for(right_, 0) <= temp_limit && cm_i32_code_count(right_pc) && cm_i32_code_count(right_pc + Zlength(cm_expr_code_for(policy, p, fid, right_pc, right_temp, right_, 0))) && emp */
  cm_emit_expr(program, fid, fn, right_pc, right_temp, temp_limit,
                 right_expr, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = right_, body = body, next = next, functions_ptr = functions_ptr, done = app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 1)), cm_temp_store_code(policy, p, fid, temp)), tail = app(cm_char_normalize_code(ty_), app(cm_temp_load_code(policy, p, fid, temp), app(cm_store_code(ty_), app(cm_temp_load_code(policy, p, fid, temp), app(cm_load_code(ty_), tail))))), out = out, capacity = capacity */;
    cm_emit_normalize_plan(emitter, expr->ty) /*@ where policy = policy, p = p, done = app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 1)), cm_temp_store_code(policy, p, fid, temp)), cm_expr_code_for(policy, p, fid, pc + (left_count + 5), temp + 1, right_, 0)), tail = app(cm_temp_load_code(policy, p, fid, temp), app(cm_store_code(ty_), app(cm_temp_load_code(policy, p, fid, temp), app(cm_load_code(ty_), tail)))), out = out, capacity = capacity, model_ty = ty_ */;
    cm_emit_temp_load_plan(fn, temp, emitter) /*@ where policy = policy, p = p, done = app(app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 1)), cm_temp_store_code(policy, p, fid, temp)), cm_expr_code_for(policy, p, fid, pc + (left_count + 5), temp + 1, right_, 0)), cm_char_normalize_code(ty_)), tail = app(cm_store_code(ty_), app(cm_temp_load_code(policy, p, fid, temp), app(cm_load_code(ty_), tail))), out = out, capacity = capacity, f = f, fid = fid, structs = cm_program_structs(p), body = body, next = next */;
    cm_emit_store_plan(emitter, expr->ty) /*@ where policy = policy, p = p, done = app(app(app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 1)), cm_temp_store_code(policy, p, fid, temp)), cm_expr_code_for(policy, p, fid, pc + (left_count + 5), temp + 1, right_, 0)), cm_char_normalize_code(ty_)), cm_temp_load_code(policy, p, fid, temp)), tail = app(cm_temp_load_code(policy, p, fid, temp), app(cm_load_code(ty_), tail)), out = out, capacity = capacity, model_ty = ty_ */;
    cm_emit_temp_load_plan(fn, temp, emitter) /*@ where policy = policy, p = p, done = app(app(app(app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 1)), cm_temp_store_code(policy, p, fid, temp)), cm_expr_code_for(policy, p, fid, pc + (left_count + 5), temp + 1, right_, 0)), cm_char_normalize_code(ty_)), cm_temp_load_code(policy, p, fid, temp)), cm_store_code(ty_)), tail = app(cm_load_code(ty_), tail), out = out, capacity = capacity, f = f, fid = fid, structs = cm_program_structs(p), body = body, next = next */;
    cm_emit_load_plan(emitter, expr->ty) /*@ where policy = policy, p = p, done = app(app(app(app(app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 1)), cm_temp_store_code(policy, p, fid, temp)), cm_expr_code_for(policy, p, fid, pc + (left_count + 5), temp + 1, right_, 0)), cm_char_normalize_code(ty_)), cm_temp_load_code(policy, p, fid, temp)), cm_store_code(ty_)), cm_temp_load_code(policy, p, fid, temp)), tail = tail, out = out, capacity = capacity, model_ty = ty_ */;
  } else {
  }

  
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && cm_expr_shape(e, CMAssignE(left_, right_, ty_)) && xargs == 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_rep(xa, left_) * cm_expr_rep(xb, right_)
      which implies cm_expr_rep(expr, e) */
}



static void cm_emit_binary_expr(struct cm_program *program, int fid,
                                struct cm_function *fn, int pc, int temp,
                                int temp_limit, struct cm_expr *expr,
                                int lvalue, struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (op_ : Z) (left_ : cm_expr) (right_ : cm_expr) (ty_ : cm_type) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require e == CMBinaryE(op_, left_, right_, ty_) && 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
 Ensure e == CMBinaryE(op_, left_, right_, ty_) && 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue)), tail)
*/
{
  /*@ cm_expr_shape(e, CMBinaryE(op_, left_, right_, ty_)) && cm_expr_rep(expr, e)
      which implies exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && cm_expr_shape(e, CMBinaryE(op_, left_, right_, ty_)) && xargs == 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, op_) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_rep(xa, left_) * cm_expr_rep(xb, right_) */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMBinaryE(op_, left_, right_, ty_)) && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMBinaryE(op_, left_, right_, ty_)) && 0 <= temp_limit && temp_limit <= 2147483647 && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_type_code_wf(cm_expr_type(e)) && cm_type_refs(cm_program_structs(p), cm_expr_type(e)) && cm_expr_wf(policy, p, f, left_) && cm_expr_counts_representable(policy, p, fid, left_) && cm_type_code_wf(cm_expr_type(left_)) && cm_type_refs(cm_program_structs(p), cm_expr_type(left_)) && cm_i32_code_count(cm_type_encode(cm_expr_type(left_))) && cm_expr_wf(policy, p, f, right_) && cm_expr_counts_representable(policy, p, fid, right_) && cm_type_code_wf(cm_expr_type(right_)) && cm_type_refs(cm_program_structs(p), cm_expr_type(right_)) && cm_i32_code_count(cm_type_encode(cm_expr_type(right_))) && cm_expr_type(e) == ty_ && cm_type_code_wf(ty_) && cm_type_refs(cm_program_structs(p), ty_) && cm_rep_expr_op(e) == op_ && emp */
  

  if (!lvalue) {
    int left_count = cm_expr_rvalue_count_context(
        program, fid, fn, expr->a) /*@ where policy = policy, cg = cg, p = p, f = f, e = left_, body = body, next = next, functions_ptr = functions_ptr */;
    int right_count = cm_expr_rvalue_count_context(
        program, fid, fn, expr->b) /*@ where policy = policy, cg = cg, p = p, f = f, e = right_, body = body, next = next, functions_ptr = functions_ptr */;
    if (expr->op == CMC_BIN_OR || expr->op == CMC_BIN_AND) {
      if (expr->op == CMC_BIN_OR) {
      } else {
      }
      
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMBinaryE(op_, left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && (0 <= op_ && op_ <= 1) && left_count == cm_rvalue_code_count(policy, p, fid, left_) && right_count == cm_rvalue_code_count(policy, p, fid, right_) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMBinaryE(op_, left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && (0 <= op_ && op_ <= 1) && left_count == cm_rvalue_code_count(policy, p, fid, left_) && right_count == cm_rvalue_code_count(policy, p, fid, right_) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, left_, 0), cons(TVMInst(cm_short_opcode(op_), pc + (left_count + (right_count + 4))), app(cm_expr_code_for(policy, p, fid, pc + (left_count + 1), temp, right_, 0), cons(TVMInst(TVMPushOp, 0), cons(TVMInst(TVMNeOp, 0), cons(TVMInst(TVMJmpOp, pc + (left_count + (right_count + 5))), cons(TVMInst(TVMPushOp, cm_short_value(op_)), tail)))))))) */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMBinaryE(op_, left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && (0 <= op_ && op_ <= 1) && left_count == cm_rvalue_code_count(policy, p, fid, left_) && right_count == cm_rvalue_code_count(policy, p, fid, right_) && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMBinaryE(op_, left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && (0 <= op_ && op_ <= 1) && left_count == cm_rvalue_code_count(policy, p, fid, left_) && right_count == cm_rvalue_code_count(policy, p, fid, right_) && 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(left_, 0) <= temp_limit && cm_i32_code_count(pc) && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, left_, 0))) && emp */
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = left_, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = cons(TVMInst(cm_short_opcode(op_), pc + (left_count + (right_count + 4))), app(cm_expr_code_for(policy, p, fid, pc + (left_count + 1), temp, right_, 0), cons(TVMInst(TVMPushOp, 0), cons(TVMInst(TVMNeOp, 0), cons(TVMInst(TVMJmpOp, pc + (left_count + (right_count + 5))), cons(TVMInst(TVMPushOp, cm_short_value(op_)), tail)))))), out = out, capacity = capacity */;
      long long first_target =
          (long long)pc +
          ((long long)left_count + ((long long)right_count + 4LL));
      if (expr->op == CMC_BIN_OR) {
        cm_emit_plan(emitter, CMC_OP_JNZ, first_target) /*@ where policy = policy, p = p, done = app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), tail = app(cm_expr_code_for(policy, p, fid, pc + (left_count + 1), temp, right_, 0), cons(TVMInst(TVMPushOp, 0), cons(TVMInst(TVMNeOp, 0), cons(TVMInst(TVMJmpOp, pc + (left_count + (right_count + 5))), cons(TVMInst(TVMPushOp, cm_short_value(op_)), tail))))), out = out, capacity = capacity, opcode = cm_short_opcode(op_) */;
      } else {
        cm_emit_plan(emitter, CMC_OP_JZ, first_target) /*@ where policy = policy, p = p, done = app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), tail = app(cm_expr_code_for(policy, p, fid, pc + (left_count + 1), temp, right_, 0), cons(TVMInst(TVMPushOp, 0), cons(TVMInst(TVMNeOp, 0), cons(TVMInst(TVMJmpOp, pc + (left_count + (right_count + 5))), cons(TVMInst(TVMPushOp, cm_short_value(op_)), tail))))), out = out, capacity = capacity, opcode = cm_short_opcode(op_) */;
      }
      int right_pc = pc + (left_count + 1);
      struct cm_expr *right_expr = expr->b;
      if (expr->op == CMC_BIN_OR) {
        
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMBinaryE(op_, left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && (0 <= op_ && op_ <= 1) && left_count == cm_rvalue_code_count(policy, p, fid, left_) && right_count == cm_rvalue_code_count(policy, p, fid, right_) && right_pc == pc + (left_count + 1) && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMBinaryE(op_, left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && (0 <= op_ && op_ <= 1) && left_count == cm_rvalue_code_count(policy, p, fid, left_) && right_count == cm_rvalue_code_count(policy, p, fid, right_) && right_pc == pc + (left_count + 1) && 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(right_, 0) <= temp_limit && cm_i32_code_count(right_pc) && cm_i32_code_count(right_pc + Zlength(cm_expr_code_for(policy, p, fid, right_pc, temp, right_, 0))) && emp */
  cm_emit_expr(program, fid, fn, right_pc, temp,
                     temp_limit, right_expr, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = right_, body = body, next = next, functions_ptr = functions_ptr, done = app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), cons(TVMInst(cm_short_opcode(op_), pc + (left_count + (right_count + 4))), nil)), tail = cons(TVMInst(TVMPushOp, 0), cons(TVMInst(TVMNeOp, 0), cons(TVMInst(TVMJmpOp, pc + (left_count + (right_count + 5))), cons(TVMInst(TVMPushOp, cm_short_value(op_)), tail)))), out = out, capacity = capacity */;
      } else {
        
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMBinaryE(op_, left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && (0 <= op_ && op_ <= 1) && left_count == cm_rvalue_code_count(policy, p, fid, left_) && right_count == cm_rvalue_code_count(policy, p, fid, right_) && right_pc == pc + (left_count + 1) && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMBinaryE(op_, left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && (0 <= op_ && op_ <= 1) && left_count == cm_rvalue_code_count(policy, p, fid, left_) && right_count == cm_rvalue_code_count(policy, p, fid, right_) && right_pc == pc + (left_count + 1) && 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(right_, 0) <= temp_limit && cm_i32_code_count(right_pc) && cm_i32_code_count(right_pc + Zlength(cm_expr_code_for(policy, p, fid, right_pc, temp, right_, 0))) && emp */
  cm_emit_expr(program, fid, fn, right_pc, temp,
                     temp_limit, right_expr, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = right_, body = body, next = next, functions_ptr = functions_ptr, done = app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), cons(TVMInst(cm_short_opcode(op_), pc + (left_count + (right_count + 4))), nil)), tail = cons(TVMInst(TVMPushOp, 0), cons(TVMInst(TVMNeOp, 0), cons(TVMInst(TVMJmpOp, pc + (left_count + (right_count + 5))), cons(TVMInst(TVMPushOp, cm_short_value(op_)), tail)))), out = out, capacity = capacity */;
      }
      cm_emit_plan(emitter, CMC_OP_PUSH, 0) /*@ where policy = policy, p = p, done = app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), cons(TVMInst(cm_short_opcode(op_), pc + (left_count + (right_count + 4))), nil)), cm_expr_code_for(policy, p, fid, pc + (left_count + 1), temp, right_, 0)), tail = cons(TVMInst(TVMNeOp, 0), cons(TVMInst(TVMJmpOp, pc + (left_count + (right_count + 5))), cons(TVMInst(TVMPushOp, cm_short_value(op_)), tail))), out = out, capacity = capacity, opcode = TVMPushOp */;
      cm_emit_plan(emitter, CMC_OP_NE, 0) /*@ where policy = policy, p = p, done = app(app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), cons(TVMInst(cm_short_opcode(op_), pc + (left_count + (right_count + 4))), nil)), cm_expr_code_for(policy, p, fid, pc + (left_count + 1), temp, right_, 0)), cons(TVMInst(TVMPushOp, 0), nil)), tail = cons(TVMInst(TVMJmpOp, pc + (left_count + (right_count + 5))), cons(TVMInst(TVMPushOp, cm_short_value(op_)), tail)), out = out, capacity = capacity, opcode = TVMNeOp */;
      long long final_target =
          (long long)pc +
          ((long long)left_count + ((long long)right_count + 5LL));
      cm_emit_plan(emitter, CMC_OP_JMP, final_target) /*@ where policy = policy, p = p, done = app(app(app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), cons(TVMInst(cm_short_opcode(op_), pc + (left_count + (right_count + 4))), nil)), cm_expr_code_for(policy, p, fid, pc + (left_count + 1), temp, right_, 0)), cons(TVMInst(TVMPushOp, 0), nil)), cons(TVMInst(TVMNeOp, 0), nil)), tail = cons(TVMInst(TVMPushOp, cm_short_value(op_)), tail), out = out, capacity = capacity, opcode = TVMJmpOp */;
      long long short_value =
          expr->op == CMC_BIN_OR ? 1LL : 0LL;
      /*@ cm_short_value(op_) <= short_value && short_value <= cm_short_value(op_) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(app(app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), cons(TVMInst(cm_short_opcode(op_), pc + (left_count + (right_count + 4))), nil)), cm_expr_code_for(policy, p, fid, pc + (left_count + 1), temp, right_, 0)), cons(TVMInst(TVMPushOp, 0), nil)), cons(TVMInst(TVMNeOp, 0), nil)), cons(TVMInst(TVMJmpOp, pc + (left_count + (right_count + 5))), nil)), cons(TVMInst(TVMPushOp, cm_short_value(op_)), tail))
      which implies cm_short_value(op_) <= short_value && short_value <= cm_short_value(op_) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(app(app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), cons(TVMInst(cm_short_opcode(op_), pc + (left_count + (right_count + 4))), nil)), cm_expr_code_for(policy, p, fid, pc + (left_count + 1), temp, right_, 0)), cons(TVMInst(TVMPushOp, 0), nil)), cons(TVMInst(TVMNeOp, 0), nil)), cons(TVMInst(TVMJmpOp, pc + (left_count + (right_count + 5))), nil)), cons(TVMInst(TVMPushOp, short_value), tail)) */
      cm_emit_plan(emitter, CMC_OP_PUSH, short_value) /*@ where policy = policy, p = p, done = app(app(app(app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), cons(TVMInst(cm_short_opcode(op_), pc + (left_count + (right_count + 4))), nil)), cm_expr_code_for(policy, p, fid, pc + (left_count + 1), temp, right_, 0)), cons(TVMInst(TVMPushOp, 0), nil)), cons(TVMInst(TVMNeOp, 0), nil)), cons(TVMInst(TVMJmpOp, pc + (left_count + (right_count + 5))), nil)), tail = tail, out = out, capacity = capacity, opcode = TVMPushOp */;
      if (expr->op == CMC_BIN_OR) {
      } else {
      }
    } else {
      
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMBinaryE(op_, left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && op_ != 0 && op_ != 1 && left_count == cm_rvalue_code_count(policy, p, fid, left_) && right_count == cm_rvalue_code_count(policy, p, fid, right_) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMBinaryE(op_, left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && op_ != 0 && op_ != 1 && left_count == cm_rvalue_code_count(policy, p, fid, left_) && right_count == cm_rvalue_code_count(policy, p, fid, right_) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, left_, 0), app(cm_temp_store_code(policy, p, fid, temp), app(cm_expr_code_for(policy, p, fid, pc + (left_count + 5), temp + 1, right_, 0), app(cm_binary_finish_code(policy, p, fid, op_, left_, right_, temp), tail))))) */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMBinaryE(op_, left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && op_ != 0 && op_ != 1 && left_count == cm_rvalue_code_count(policy, p, fid, left_) && right_count == cm_rvalue_code_count(policy, p, fid, right_) && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMBinaryE(op_, left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && op_ != 0 && op_ != 1 && left_count == cm_rvalue_code_count(policy, p, fid, left_) && right_count == cm_rvalue_code_count(policy, p, fid, right_) && 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(left_, 0) <= temp_limit && cm_i32_code_count(pc) && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, left_, 0))) && emp */
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = left_, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = app(cm_temp_store_code(policy, p, fid, temp), app(cm_expr_code_for(policy, p, fid, pc + (left_count + 5), temp + 1, right_, 0), app(cm_binary_finish_code(policy, p, fid, op_, left_, right_, temp), tail))), out = out, capacity = capacity */;
      cm_emit_temp_store_plan(fn, temp, emitter) /*@ where policy = policy, p = p, done = app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), tail = app(cm_expr_code_for(policy, p, fid, pc + (left_count + 5), temp + 1, right_, 0), app(cm_binary_finish_code(policy, p, fid, op_, left_, right_, temp), tail)), out = out, capacity = capacity, f = f, fid = fid, structs = cm_program_structs(p), body = body, next = next */;
      int right_pc = pc + (left_count + 5);
      int right_temp = temp + 1;
      struct cm_expr *right_expr = expr->b;
      
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMBinaryE(op_, left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && op_ != 0 && op_ != 1 && left_count == cm_rvalue_code_count(policy, p, fid, left_) && right_count == cm_rvalue_code_count(policy, p, fid, right_) && right_pc == pc + (left_count + 5) && right_temp == temp + 1 && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMBinaryE(op_, left_, right_, ty_)) && 0 <= lvalue && lvalue <= 0 && op_ != 0 && op_ != 1 && left_count == cm_rvalue_code_count(policy, p, fid, left_) && right_count == cm_rvalue_code_count(policy, p, fid, right_) && right_pc == pc + (left_count + 5) && right_temp == temp + 1 && 0 <= right_temp && right_temp <= temp_limit && right_temp + cm_expr_temps_for(right_, 0) <= temp_limit && cm_i32_code_count(right_pc) && cm_i32_code_count(right_pc + Zlength(cm_expr_code_for(policy, p, fid, right_pc, right_temp, right_, 0))) && emp */
  cm_emit_expr(program, fid, fn, right_pc, right_temp,
                   temp_limit, right_expr, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = right_, body = body, next = next, functions_ptr = functions_ptr, done = app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), cm_temp_store_code(policy, p, fid, temp)), tail = app(cm_binary_finish_code(policy, p, fid, op_, left_, right_, temp), tail), out = out, capacity = capacity */;
      cm_emit_binary_finish_plan(program, fid, fn, temp, expr->op,
                                 expr->a, expr->b, emitter) /*@ where policy = policy, p = p, done = app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, left_, 0)), cm_temp_store_code(policy, p, fid, temp)), cm_expr_code_for(policy, p, fid, pc + (left_count + 5), temp + 1, right_, 0)), tail = tail, out = out, capacity = capacity, f = f, body = body, next = next, left_e = left_, right_e = right_, functions_ptr = functions_ptr */;
    }
  } else {
  }

  
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && cm_expr_shape(e, CMBinaryE(op_, left_, right_, ty_)) && xargs == 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, op_) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_rep(xa, left_) * cm_expr_rep(xb, right_)
      which implies cm_expr_rep(expr, e) */
}



static void cm_emit_member_expr(struct cm_program *program, int fid,
                                struct cm_function *fn, int pc, int temp,
                                int temp_limit, struct cm_expr *expr,
                                int lvalue, struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (arg_ : cm_expr) (mid_ : Z) (ty_ : cm_type) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require e == CMMemberE(arg_, mid_, ty_) && 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
 Ensure e == CMMemberE(arg_, mid_, ty_) && 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue)), tail)
*/
{
  /*@ cm_expr_shape(e, CMMemberE(arg_, mid_, ty_)) && cm_expr_rep(expr, e)
      which implies exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && cm_expr_shape(e, CMMemberE(arg_, mid_, ty_)) && xa != 0 && xb == 0 && xargs == 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_rep(xa, arg_) */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMMemberE(arg_, mid_, ty_)) && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMMemberE(arg_, mid_, ty_)) && 0 <= temp_limit && temp_limit <= 2147483647 && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_type_code_wf(cm_expr_type(e)) && cm_type_refs(cm_program_structs(p), cm_expr_type(e)) && cm_expr_wf(policy, p, f, arg_) && cm_expr_counts_representable(policy, p, fid, arg_) && cm_type_code_wf(cm_expr_type(arg_)) && cm_type_refs(cm_program_structs(p), cm_expr_type(arg_)) && cm_i32_code_count(cm_type_encode(cm_expr_type(arg_))) && 0 <= mid_ && mid_ <= 2147483647 && cm_member_valid(p, cm_expr_type(arg_), mid_) && cm_rep_expr_value(e) == mid_ && cm_expr_type(e) == ty_ && cm_type_code_wf(ty_) && cm_type_refs(cm_program_structs(p), ty_) && emp */
  

  int member_id = (int)expr->value;
  int base_type;
  cm_expr_type_code_context(expr->a, &base_type) /*@ where e = arg_ */;
  int array_value = cm_member_array_value_context(
      program, base_type, member_id) /*@ where policy = policy, p = p, base = cm_expr_type(arg_), functions_ptr = functions_ptr */;
  long long offset = cm_member_offset_value_context(
      program, base_type, member_id) /*@ where policy = policy, p = p, base = cm_expr_type(arg_), functions_ptr = functions_ptr */;
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMMemberE(arg_, mid_, ty_)) && offset == cm_member_offset(cm_program_structs(p), cm_struct_id(cm_pointee(cm_expr_type(arg_))), mid_) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMMemberE(arg_, mid_, ty_)) && offset == cm_member_offset(cm_program_structs(p), cm_struct_id(cm_pointee(cm_expr_type(arg_))), mid_) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0), cons(TVMInst(TVMPushOp, offset), cons(TVMInst(TVMAddOp, 0), app(cm_member_load_suffix(p, arg_, mid_, ty_, lvalue), tail))))) */
  
  /*@ 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMMemberE(arg_, mid_, ty_)) && emp
      which implies 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_expr_shape(e, CMMemberE(arg_, mid_, ty_)) && 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(arg_, 0) <= temp_limit && cm_i32_code_count(pc) && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0))) && emp */
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
               expr->a, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = arg_, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = cons(TVMInst(TVMPushOp, offset), cons(TVMInst(TVMAddOp, 0), app(cm_member_load_suffix(p, arg_, mid_, ty_, lvalue), tail))), out = out, capacity = capacity */;
  cm_emit_plan(emitter, CMC_OP_PUSH, offset) /*@ where policy = policy, p = p, done = app(done, cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0)), tail = cons(TVMInst(TVMAddOp, 0), app(cm_member_load_suffix(p, arg_, mid_, ty_, lvalue), tail)), out = out, capacity = capacity, opcode = TVMPushOp */;
  cm_emit_plan(emitter, CMC_OP_ADD, 0) /*@ where policy = policy, p = p, done = app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0)), cons(TVMInst(TVMPushOp, offset), nil)), tail = app(cm_member_load_suffix(p, arg_, mid_, ty_, lvalue), tail), out = out, capacity = capacity, opcode = TVMAddOp */;
  if (!lvalue) {
    if (!array_value) {
      
  /*@ 0 <= lvalue && lvalue <= 0 && array_value == 0 && array_value == cm_member_array_code(p, cm_expr_type(arg_), mid_) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0)), cons(TVMInst(TVMPushOp, offset), nil)), cons(TVMInst(TVMAddOp, 0), nil)), app(cm_member_load_suffix(p, arg_, mid_, ty_, lvalue), tail))
      which implies 0 <= lvalue && lvalue <= 0 && array_value == 0 && array_value == cm_member_array_code(p, cm_expr_type(arg_), mid_) && 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0)), cons(TVMInst(TVMPushOp, offset), nil)), cons(TVMInst(TVMAddOp, 0), nil)), app(cm_load_code(ty_), tail)) */
  cm_emit_load_plan(emitter, expr->ty) /*@ where policy = policy, p = p, done = app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, arg_, 0)), cons(TVMInst(TVMPushOp, offset), nil)), cons(TVMInst(TVMAddOp, 0), nil)), tail = tail, out = out, capacity = capacity, model_ty = ty_ */;
    } else {
    }
  } else {
  }

  
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && cm_expr_shape(e, CMMemberE(arg_, mid_, ty_)) && xa != 0 && xb == 0 && xargs == 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_rep(xa, arg_)
      which implies cm_expr_rep(expr, e) */
}



void cm_emit_expr(struct cm_program *program, int fid,
                  struct cm_function *fn, int pc, int temp,
                  int temp_limit, struct cm_expr *expr, int lvalue,
                  struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
 Ensure 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue)), tail)
*/
{
  /*@ cm_expr_rep(expr, e)
      which implies exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs) */

  if (expr->kind == CMC_EXPR_CONST) {
    
  /*@ pc == pc@pre && temp == temp@pre && cm_rep_expr_kind(e) == 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
      which implies exists (simple : cm_simple_view), pc == pc@pre && temp == temp@pre && e == cm_simple_source_expr(simple) && cm_simple_expr(e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_simple_code_for(policy, p, fid, simple, lvalue), tail)) */
  
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
      which implies cm_expr_rep(expr, e) */
  cm_emit_simple_expr(program, fid, fn, pc, temp,
        expr, lvalue, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity */;
  } else if (expr->kind == CMC_EXPR_STRING) {
    
  /*@ pc == pc@pre && temp == temp@pre && cm_rep_expr_kind(e) == 1 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
      which implies exists (simple : cm_simple_view), pc == pc@pre && temp == temp@pre && e == cm_simple_source_expr(simple) && cm_simple_expr(e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_simple_code_for(policy, p, fid, simple, lvalue), tail)) */
  
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
      which implies cm_expr_rep(expr, e) */
  cm_emit_simple_expr(program, fid, fn, pc, temp,
        expr, lvalue, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity */;
  } else if (expr->kind == CMC_EXPR_VAR) {
    
  /*@ pc == pc@pre && temp == temp@pre && cm_rep_expr_kind(e) == 2 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
      which implies exists (simple : cm_simple_view), pc == pc@pre && temp == temp@pre && e == cm_simple_source_expr(simple) && cm_simple_expr(e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_simple_code_for(policy, p, fid, simple, lvalue), tail)) */
  
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
      which implies cm_expr_rep(expr, e) */
  cm_emit_simple_expr(program, fid, fn, pc, temp,
        expr, lvalue, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity */;
  } else if (expr->kind == CMC_EXPR_ASSIGN) {
    
  /*@ cm_rep_expr_kind(e) == 3 && emp
      which implies cm_expr_shape(e, CMAssignE(cm_expr_child(e), cm_expr_second(e), cm_expr_type(e))) && emp */
  
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
      which implies cm_expr_rep(expr, e) */
  cm_emit_assignment_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity, left_ = cm_expr_child(e), right_ = cm_expr_second(e), ty_ = cm_expr_type(e) */;
  } else if (expr->kind == CMC_EXPR_BINARY) {
    
  /*@ cm_rep_expr_kind(e) == 4 && emp
      which implies cm_expr_shape(e, CMBinaryE(cm_rep_expr_op(e), cm_expr_child(e), cm_expr_second(e), cm_expr_type(e))) && emp */
  
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
      which implies cm_expr_rep(expr, e) */
  cm_emit_binary_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity, op_ = cm_rep_expr_op(e), left_ = cm_expr_child(e), right_ = cm_expr_second(e), ty_ = cm_expr_type(e) */;
  } else if (expr->kind == CMC_EXPR_UNARY) {
    
  /*@ cm_rep_expr_kind(e) == 5 && emp
      which implies cm_expr_shape(e, CMUnaryE(cm_rep_expr_op(e), cm_expr_child(e), cm_expr_type(e))) && emp */
  
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
      which implies cm_expr_rep(expr, e) */
  cm_emit_unary_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity, op_ = cm_rep_expr_op(e), arg_ = cm_expr_child(e), ty_ = cm_expr_type(e) */;
  } else if (expr->kind == CMC_EXPR_INDEX) {
    
  /*@ cm_rep_expr_kind(e) == 6 && emp
      which implies cm_expr_shape(e, CMIndexE(cm_expr_child(e), cm_expr_second(e), cm_expr_type(e))) && emp */
  
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
      which implies cm_expr_rep(expr, e) */
  cm_emit_index_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity, left_ = cm_expr_child(e), right_ = cm_expr_second(e), ty_ = cm_expr_type(e) */;
  } else if (expr->kind == CMC_EXPR_MEMBER) {
    
  /*@ cm_rep_expr_kind(e) == 7 && emp
      which implies cm_expr_shape(e, CMMemberE(cm_expr_child(e), cm_rep_expr_value(e), cm_expr_type(e))) && emp */
  
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
      which implies cm_expr_rep(expr, e) */
  cm_emit_member_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity, arg_ = cm_expr_child(e), ty_ = cm_expr_type(e), mid_ = cm_rep_expr_value(e) */;
  } else if (expr->kind == CMC_EXPR_CALL) {
    
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
      which implies cm_expr_rep(expr, e) */
  cm_emit_call_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity */;
  } else if (expr->kind == CMC_EXPR_SIZEOF) {
    
  /*@ pc == pc@pre && temp == temp@pre && cm_rep_expr_kind(e) == 9 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
      which implies exists (simple : cm_simple_view), pc == pc@pre && temp == temp@pre && e == cm_simple_source_expr(simple) && cm_simple_expr(e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_simple_code_for(policy, p, fid, simple, lvalue), tail)) */
  
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
      which implies cm_expr_rep(expr, e) */
  cm_emit_simple_expr(program, fid, fn, pc, temp,
        expr, lvalue, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity */;
  } else if (expr->kind == CMC_EXPR_GETC) {
    
  /*@ pc == pc@pre && temp == temp@pre && cm_rep_expr_kind(e) == 10 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
      which implies exists (simple : cm_simple_view), pc == pc@pre && temp == temp@pre && e == cm_simple_source_expr(simple) && cm_simple_expr(e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_simple_code_for(policy, p, fid, simple, lvalue), tail)) */
  
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
      which implies cm_expr_rep(expr, e) */
  cm_emit_simple_expr(program, fid, fn, pc, temp,
        expr, lvalue, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity */;
  } else if (expr->kind == CMC_EXPR_PUTC) {
    
  /*@ cm_rep_expr_kind(e) == 11 && emp
      which implies cm_intrinsic_expr(e) && emp */
  
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
      which implies cm_expr_rep(expr, e) */
  cm_emit_intrinsic_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity */;
  } else if (expr->kind == CMC_EXPR_PUTI) {
    
  /*@ cm_rep_expr_kind(e) == 12 && emp
      which implies cm_intrinsic_expr(e) && emp */
  
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
      which implies cm_expr_rep(expr, e) */
  cm_emit_intrinsic_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity */;
  } else {
    
  /*@ cm_rep_expr_kind(e) != 0 && cm_rep_expr_kind(e) != 1 && cm_rep_expr_kind(e) != 2 && cm_rep_expr_kind(e) != 3 && cm_rep_expr_kind(e) != 4 && cm_rep_expr_kind(e) != 5 && cm_rep_expr_kind(e) != 6 && cm_rep_expr_kind(e) != 7 && cm_rep_expr_kind(e) != 8 && cm_rep_expr_kind(e) != 9 && cm_rep_expr_kind(e) != 10 && cm_rep_expr_kind(e) != 11 && cm_rep_expr_kind(e) != 12 && emp
      which implies cm_intrinsic_expr(e) && emp */
  
  /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, xa) * data_at(&(expr->b), struct cm_expr *, xb) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
      which implies cm_expr_rep(expr, e) */
  cm_emit_intrinsic_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity */;
  }
}

