#pragma once

#include "cmc_concrete_layout.h"
#require "cmc_concrete_layout.c"



PROOF void cm_commit_arith_fact(const char *chain);
PROOF extern thm get_cm_concrete_function_ready_def(void);
PROOF extern thm get_cm_concrete_functions_ready_def(void);

int cm_expr_lvalue_count(struct cm_program *program, int fid,
                                struct cm_function *fn,
                                struct cm_expr *expr)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `structs:(cm_struct_d)list`,
                 `globals:(cm_global_d)list`,
                 `locals:(cm_slot_d)list`,
                 `zs:int`, `zg:int`, `zl:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       cm_expr_rep expr e`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       cm_expr_rep expr e **
       fact((__return:int) ==
         cm_lcount_of (cm_expr_code_counts p fid e)) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]];

int cm_expr_rvalue_count(struct cm_program *program, int fid,
                                struct cm_function *fn,
                                struct cm_expr *expr)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `structs:(cm_struct_d)list`,
                 `globals:(cm_global_d)list`,
                 `locals:(cm_slot_d)list`,
                 `zs:int`, `zg:int`, `zl:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       cm_expr_rep expr e`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       cm_expr_rep expr e **
       fact((__return:int) ==
         cm_rcount_of (cm_expr_code_counts p fid e)) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]];

int cmc_function_pc(struct cm_program *program, int fid)
    [[cst::param(`p:cm_program`, `functions_ptr:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       fact(0i <= fid) **
       fact(fid <= ilength (cm_program_functions p)) **
       fact(cm_i32_code_count
              (cm_function_pc p fid) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr
         (cm_program_functions p)`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       fact(0i <= fid) **
       fact(fid <= ilength (cm_program_functions p)) **
       fact(cm_i32_code_count
              (cm_function_pc p fid) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr
         (cm_program_functions p) **
       fact((__return:int) == cm_function_pc p fid) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]];

int cmc_function_prologue_count(struct cm_function *fn)
    [[cst::param(`f:cm_function_d`, `body:int`, `next:int`)]]
    [[cst::require(
      `fact(cm_param_counts_representable
              (cm_function_params f) <=> true) **
       fact(cm_i32_code_count
              (cm_function_prologue_count f) <=> true) **
       cm_function_context_rep fn f body next`)]]
    [[cst::ensure(
      `fact(cm_param_counts_representable
              (cm_function_params f) <=> true) **
       fact(cm_i32_code_count
              (cm_function_prologue_count f) <=> true) **
       cm_function_context_rep fn f body next **
       fact((__return:int) == cm_function_prologue_count f) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]];

int cmc_function_code_count(struct cm_program *program, int fid,
                            struct cm_function *fn)
    [[cst::param(`p:cm_program`, `f:cm_function_d`,
                 `functions_ptr:int`, `body_ptr:int`,
                 `next_ptr:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_function_counts_representable p fid f <=> true) **
       fact(cm_stmt_wf p f F (cm_function_body f) <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body_ptr next_ptr **
       cm_stmt_rep body_ptr (cm_function_body f)`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_function_counts_representable p fid f <=> true) **
       fact(cm_stmt_wf p f F (cm_function_body f) <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body_ptr next_ptr **
       cm_stmt_rep body_ptr (cm_function_body f) **
       fact((__return:int) == cm_function_code_count p fid) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]];

int cmc_model_code_length(struct cm_program *program)
    [[cst::param(`p:cm_program`, `functions_ptr:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr
         (cm_program_functions p)`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr
         (cm_program_functions p) **
       fact((__return:int) == cm_model_code_length p) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]];

int cmc_model_data_length(struct cm_program *program)
    [[cst::param(`p:cm_program`, `functions_ptr:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_rep_globals_safe
              (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe
              (cm_program_strings p) <=> true) **
       fact(cm_model_data_length p ==
         (8i + cm_rep_globals_size
           (cm_program_globals p)) +
         cm_rep_strings_size
           (cm_program_strings p)) **
       cm_program_context_rep program p functions_ptr`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_rep_globals_safe
              (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe
              (cm_program_strings p) <=> true) **
       fact(cm_model_data_length p ==
         (8i + cm_rep_globals_size
           (cm_program_globals p)) +
         cm_rep_strings_size
           (cm_program_strings p)) **
       cm_program_context_rep program p functions_ptr **
       fact((__return:int) == cm_model_data_length p) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]];

int cmc_stmt_code_count(struct cm_program *program, int fid,
                               struct cm_function *fn,
                               struct cm_stmt *stmt)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `s:cm_stmt`,
                 `loop_:bool`, `structs:(cm_struct_d)list`,
                 `globals:(cm_global_d)list`,
                 `locals:(cm_slot_d)list`,
                 `zs:int`, `zg:int`, `zl:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(cm_stmt_wf p f loop_ s <=> true) **
       fact(cm_stmt_counts_representable p fid s <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Fret_ty) Tint
         (cm_type_encode (cm_function_ret f)) **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       cm_stmt_rep stmt s`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(cm_stmt_wf p f loop_ s <=> true) **
       fact(cm_stmt_counts_representable p fid s <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       fact(cm_i32_code_count (cm_stmt_code_count p fid s) <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Fret_ty) Tint
         (cm_type_encode (cm_function_ret f)) **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       cm_stmt_rep stmt s **
       fact((__return:int) == cm_stmt_code_count p fid s)`)]];

PROOF thm cm_rep_slot_type_model(
    const term slots, const term index);
PROOF void cm_open_stmt_case_st(const thm shape, int kind);
PROOF void cm_close_stmt_case_st(const thm shape, int kind);
