#pragma once

#include "cmc_concrete_emit_stmt.h"

void cmc_emit_if_stmt(struct cm_program *program, int fid,
                      struct cm_function *fn, int pc, int temp,
                      int temp_limit, int break_pc, int continue_pc,
                      struct cm_stmt *stmt, struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `s:cm_stmt`,
                 `guard_:cm_expr`, `yes_:cm_stmt`, `no_:cm_stmt`,
                 `loop_:bool`, `body:int`, `next:int`,
                 `functions_ptr:int`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(s == CMIfS guard_ yes_ no_) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_stmt_wf p f loop_ s <=> true) **
       fact(cm_stmt_counts_representable p fid s <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_stemps s <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count break_pc <=> true) **
       fact(cm_i32_code_count continue_pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength
                (cm_emit_stmt p fid pc temp break_pc continue_pc s))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_stmt_rep stmt s **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_emit_stmt p fid pc temp break_pc continue_pc s ++ tail)`)]]
    [[cst::ensure(
      `fact(s == CMIfS guard_ yes_ no_) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_stmt_wf p f loop_ s <=> true) **
       fact(cm_stmt_counts_representable p fid s <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_stemps s <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count break_pc <=> true) **
       fact(cm_i32_code_count continue_pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength
                (cm_emit_stmt p fid pc temp break_pc continue_pc s))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_stmt_rep stmt s **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_emit_stmt p fid pc temp break_pc continue_pc s)
         tail`)]];
