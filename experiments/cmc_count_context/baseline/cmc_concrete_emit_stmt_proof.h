#pragma once

#include "cmc_concrete_counts.h"
#include "userlib/operational.h"
#require "cmc_concrete_counts.c"

PROOF void cm_open_stmt_rep_st(void);
PROOF void cm_close_stmt_rep_st(void);
PROOF thm cm_stmt_case_wf(const thm shape);
PROOF thm cm_find_stmt_conjunct_rule(
    const thm conjunction, const term expected);
PROOF thm cm_stmt_code_shape(const thm shape, const term code);
PROOF thm cm_rvalue_code_length_at(
    const term expr, const term pc, const term temp);
PROOF thm cm_stmt_code_length_at(
    const term stmt, const term pc, const term temp,
    const term break_pc, const term continue_pc);
PROOF void cm_retarget_stmt_call_result_st(
    const term cell, const thm result);
PROOF void cm_add_i32_term_st(const thm predicate);
PROOF void cm_add_stmt_fragment_i32_st(
    const thm code_shape, const term prefix,
    const term fragment, const term suffix);
