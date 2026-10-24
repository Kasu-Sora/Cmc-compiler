#pragma once

#include "cmc_concrete_emit_expr_leaf.h"
#require "cmc_concrete_emit_expr_leaf.c"

void cm_emit_binary_finish_plan(struct cm_program *program, int fid,
                                struct cm_function *fn, int temp, int op,
                                struct cm_expr *left,
                                struct cm_expr *right,
                                struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`,
                 `left_e:cm_expr`, `right_e:cm_expr`,
                 `body:int`, `next:int`, `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_type_code_wf (cm_expr_type left_e) <=> true) **
       fact(cm_type_code_wf (cm_expr_type right_e) <=> true) **
       fact(cm_type_refs (cm_program_structs p)
              (cm_expr_type left_e) <=> true) **
       fact(cm_type_refs (cm_program_structs p)
              (cm_expr_type right_e) <=> true) **
       fact(cm_i32_code_count
              (cm_type_encode (cm_expr_type left_e)) <=> true) **
       fact(cm_i32_code_count
              (cm_type_encode (cm_expr_type right_e)) <=> true) **
       fact(0i <= temp) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep left left_e **
       cm_expr_rep right right_e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_binary_finish_code p fid op left_e right_e temp ++ tail)`)]]
    [[cst::ensure(
      `fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_type_code_wf (cm_expr_type left_e) <=> true) **
       fact(cm_type_code_wf (cm_expr_type right_e) <=> true) **
       fact(cm_type_refs (cm_program_structs p)
              (cm_expr_type left_e) <=> true) **
       fact(cm_type_refs (cm_program_structs p)
              (cm_expr_type right_e) <=> true) **
       fact(cm_i32_code_count
              (cm_type_encode (cm_expr_type left_e)) <=> true) **
       fact(cm_i32_code_count
              (cm_type_encode (cm_expr_type right_e)) <=> true) **
       fact(0i <= temp) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep left left_e **
       cm_expr_rep right right_e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_binary_finish_code p fid op left_e right_e temp)
         tail`)]];
