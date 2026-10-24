#pragma once

#include "cmc_concrete_emit_ast.h"
#include "cmc_concrete_emit_plan.h"
#require "cmc_concrete_emit_ast.c"
#require "cmc_concrete_emit_plan.c"

void cm_emit_var_expr(struct cm_program *program, int fid,
                      struct cm_function *fn, int pc, int temp,
                      struct cm_expr *expr, int lvalue,
                      struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `scope:int`, `slot:int`, `ty:cm_type`,
                 `body:int`, `next:int`, `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(e == CMVarE scope slot ty) **
       fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(0i <= slot) ** fact(slot <= 2147483647i) **
       fact(cm_binding_valid p f scope slot <=> true) **
       fact(cm_type_code_wf ty <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_expr_code_for p fid pc temp e lvalue ++ tail)`)]]
    [[cst::ensure(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(e == CMVarE scope slot ty) **
       fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(0i <= slot) ** fact(slot <= 2147483647i) **
       fact(cm_binding_valid p f scope slot <=> true) **
       fact(cm_type_code_wf ty <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_expr_code_for p fid pc temp e lvalue) tail`)]];
