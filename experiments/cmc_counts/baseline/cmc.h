#pragma once

#include "cmc_abi.h"

#ifdef CSTAR_VERIFY
#require "cmc_abi.c"
#include "cmc_rep.h"
#require "cmc_rep.c"
int cmc_compile(struct cm_program *program, struct cm_output *output)
    [[cst::param(`p:cm_program`, `code_capacity:int`,
                 `data_capacity:int`)]]
    [[cst::require(
      `cm_program_rep program p **
       cm_output_pre output code_capacity data_capacity`)]]
    [[cst::ensure(
      `(fact((__return:int) == 0i) **
        cm_program_rep program p **
        cm_output_ok output code_capacity data_capacity p) ||
       (fact((__return:int) == 1i) **
        cm_program_rep program p **
        cm_output_capacity output code_capacity data_capacity p)`)]]
;
#else
int cmc_compile(struct cm_program *program, struct cm_output *output);
#endif
