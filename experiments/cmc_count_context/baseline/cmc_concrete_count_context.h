#pragma once

#include "cmc_concrete_counts.h"
#require "cmc_concrete_counts.c"

void cm_expr_type_code_context(struct cm_expr *expr, int *code)
    [[cst::param(`e:cm_expr`)]]
    [[cst::require(
      `cm_expr_rep expr e ** undef_data_at code Tint`)]]
    [[cst::ensure(
      `cm_expr_rep expr e **
       data_at code Tint (cm_type_encode (cm_expr_type e))`)]];

int cm_expr_lvalue_count_context(struct cm_program *program, int fid,
                                 struct cm_function *fn,
                                 struct cm_expr *expr)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `body:int`, `next:int`, `functions_ptr:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       fact((__return:int) ==
         cm_lcount_of (cm_expr_code_counts p fid e)) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]];

int cm_expr_rvalue_count_context(struct cm_program *program, int fid,
                                 struct cm_function *fn,
                                 struct cm_expr *expr)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `body:int`, `next:int`, `functions_ptr:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       fact((__return:int) ==
         cm_rcount_of (cm_expr_code_counts p fid e)) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]];

int cm_stmt_code_count_context(struct cm_program *program, int fid,
                               struct cm_function *fn,
                               struct cm_stmt *stmt)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `s:cm_stmt`,
                 `loop_:bool`, `body:int`, `next:int`,
                 `functions_ptr:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_stmt_wf p f loop_ s <=> true) **
       fact(cm_stmt_counts_representable p fid s <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_stmt_rep stmt s`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_stmt_wf p f loop_ s <=> true) **
       fact(cm_stmt_counts_representable p fid s <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_stmt_rep stmt s **
       fact((__return:int) == cm_stmt_code_count p fid s) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]];
