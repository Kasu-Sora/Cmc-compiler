#pragma once

#include "cmc_concrete_compile_ready.h"

int cmc_function_pc_total(struct cm_program *program, long long target)
    [[cst::param(`p:cm_program`, `functions_ptr:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_concrete_code_ready p <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr (cm_program_functions p)`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_concrete_code_ready p <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr (cm_program_functions p) **
       fact((__return:int) == cm_function_pc p target) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]];

PROOF extern thm cm_function_prefix_total_bounds;
