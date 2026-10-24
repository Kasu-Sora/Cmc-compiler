#pragma once

#include "cmc_concrete_emit_plan.h"
#require "cmc_concrete_emit_plan.c"

void cm_emit_const_expr(struct cm_program *program, int fid,
                        struct cm_function *fn, int pc, int temp,
                        struct cm_expr *expr, int lvalue,
                        struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `n:int`, `ty:cm_type`, `body:int`, `next:int`,
                 `functions_ptr:int`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(e == CMConstE n ty) **
       fact(f == inth fid (cm_program_functions p)) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_expr_code_for p fid pc temp e lvalue ++ tail)`)]]
    [[cst::ensure(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(e == CMConstE n ty) **
       fact(f == inth fid (cm_program_functions p)) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_expr_code_for p fid pc temp e lvalue) tail`)]];

void cm_emit_string_expr(struct cm_program *program, int fid,
                         struct cm_function *fn, int pc, int temp,
                         struct cm_expr *expr, int lvalue,
                         struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `sid:int`, `ty:cm_type`, `body:int`, `next:int`,
                 `functions_ptr:int`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(e == CMStringE sid ty) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(0i <= sid) ** fact(sid <= 2147483647i) **
       fact(cm_typed_program p <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_expr_code_for p fid pc temp e lvalue ++ tail)`)]]
    [[cst::ensure(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(e == CMStringE sid ty) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(0i <= sid) ** fact(sid <= 2147483647i) **
       fact(cm_typed_program p <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_expr_code_for p fid pc temp e lvalue) tail`)]];

void cm_emit_getc_expr(struct cm_program *program, int fid,
                       struct cm_function *fn, int pc, int temp,
                       struct cm_expr *expr, int lvalue,
                       struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `ty:cm_type`, `body:int`, `next:int`,
                 `functions_ptr:int`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(e == CMGetcE ty) **
       fact(f == inth fid (cm_program_functions p)) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_expr_code_for p fid pc temp e lvalue ++ tail)`)]]
    [[cst::ensure(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(e == CMGetcE ty) **
       fact(f == inth fid (cm_program_functions p)) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_expr_code_for p fid pc temp e lvalue) tail`)]];

void cm_emit_sizeof_expr(struct cm_program *program, int fid,
                         struct cm_function *fn, int pc, int temp,
                         struct cm_expr *expr, int lvalue,
                         struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `asked:cm_type`, `ty:cm_type`, `body:int`, `next:int`,
                 `functions_ptr:int`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(e == CMSizeofE asked ty) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_typed_program p <=> true) **
       fact(cm_type_code_wf asked <=> true) **
       fact(cm_type_refs (cm_program_structs p) asked <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_expr_code_for p fid pc temp e lvalue ++ tail)`)]]
    [[cst::ensure(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(e == CMSizeofE asked ty) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_typed_program p <=> true) **
       fact(cm_type_code_wf asked <=> true) **
       fact(cm_type_refs (cm_program_structs p) asked <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_expr_code_for p fid pc temp e lvalue) tail`)]];

long long cm_type_size_value(struct cm_program *program,
                             long long code)
    [[cst::param(`p:cm_program`, `asked:cm_type`,
                 `functions_ptr:int`)]]
    [[cst::require(
      `fact(code == cm_type_encode asked) **
       fact(cm_typed_program p <=> true) **
       fact(cm_type_code_wf asked <=> true) **
       fact(cm_type_refs (cm_program_structs p) asked <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr`)]]
    [[cst::ensure(
      `fact(code == cm_type_encode asked) **
       fact(cm_typed_program p <=> true) **
       fact(cm_type_code_wf asked <=> true) **
       fact(cm_type_refs (cm_program_structs p) asked <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       fact((__return:int) ==
         cm_type_size (cm_program_structs p) asked)`)]];

int cm_member_array_value_context(struct cm_program *program,
                                  int base_ty, int mid)
    [[cst::param(`p:cm_program`, `base:cm_type`,
                 `functions_ptr:int`)]]
    [[cst::require(
      `fact(base_ty == cm_type_encode base) **
       fact(cm_i32_code_count base_ty <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(cm_type_code_wf base <=> true) **
       fact(cm_member_valid p base mid <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr`)]]
    [[cst::ensure(
      `fact(base_ty == cm_type_encode base) **
       fact(cm_i32_code_count base_ty <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(cm_type_code_wf base <=> true) **
       fact(cm_member_valid p base mid <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       fact((__return:int) == cm_member_array_code p base mid)`)]];

long long cm_member_offset_value_context(struct cm_program *program,
                                         int base_ty, int mid)
    [[cst::param(`p:cm_program`, `base:cm_type`,
                 `functions_ptr:int`)]]
    [[cst::require(
      `fact(base_ty == cm_type_encode base) **
       fact(cm_i32_code_count base_ty <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(cm_type_code_wf base <=> true) **
       fact(cm_member_valid p base mid <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr`)]]
    [[cst::ensure(
      `fact(base_ty == cm_type_encode base) **
       fact(cm_i32_code_count base_ty <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(cm_type_code_wf base <=> true) **
       fact(cm_member_valid p base mid <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       fact((__return:int) ==
         cm_member_offset (cm_program_structs p)
           (cm_struct_id (cm_pointee base)) mid)`)]];
