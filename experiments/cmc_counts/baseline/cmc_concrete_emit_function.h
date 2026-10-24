#pragma once

#include "cmc_concrete_emit_stmt.h"
#include "cmc_concrete_emit_return.h"

void cmc_emit_function(
    struct cm_program *program, struct cm_function *fn,
    int fid, int function_pc, struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`,
                 `s:cm_stmt`, `body:int`, `next:int`,
                 `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(s == cm_function_body f) **
       fact(function_pc == cm_function_pc p fid) **
       fact(cm_stmt_wf p f false s <=> true) **
       fact(cm_stmt_counts_representable p fid s <=> true) **
       fact(cm_param_counts_representable
              (cm_function_params f) <=> true) **
       fact(cm_i32_code_count
              (cm_function_prologue_count f) <=> true) **
       fact(cm_i32_code_count function_pc <=> true) **
       fact(cm_i32_code_count
              (cm_function_pc p fid +
               cm_function_prologue_count f) <=> true) **
       fact(cm_i32_code_count
              ((cm_function_pc p fid +
                cm_function_prologue_count f) +
               ilength
                 (cm_emit_stmt p fid
                   (cm_function_pc p fid +
                    cm_function_prologue_count f)
                   0i 0i 0i s)) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe
              (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe
              (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe
              (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe
              (cm_function_locals f) <=> true) **
       fact(cm_rep_stmt_temps_safe s <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <=
              1048560i) **
       fact(8i + cm_rep_members_size (cm_function_params f) +
              cm_rep_members_size (cm_function_locals f) +
              8i * cm_stemps s <= 2147483647i) **
       fact(cm_temp_offset p fid (cm_stemps s) <=
              2147483647i) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_stmt_rep body s **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_emit_function p fid ++ tail)`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(s == cm_function_body f) **
       fact(function_pc == cm_function_pc p fid) **
       fact(cm_stmt_wf p f false s <=> true) **
       fact(cm_stmt_counts_representable p fid s <=> true) **
       fact(cm_param_counts_representable
              (cm_function_params f) <=> true) **
       fact(cm_i32_code_count
              (cm_function_prologue_count f) <=> true) **
       fact(cm_i32_code_count function_pc <=> true) **
       fact(cm_i32_code_count
              (cm_function_pc p fid +
               cm_function_prologue_count f) <=> true) **
       fact(cm_i32_code_count
              ((cm_function_pc p fid +
                cm_function_prologue_count f) +
               ilength
                 (cm_emit_stmt p fid
                   (cm_function_pc p fid +
                    cm_function_prologue_count f)
                   0i 0i 0i s)) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe
              (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe
              (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe
              (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe
              (cm_function_locals f) <=> true) **
       fact(cm_rep_stmt_temps_safe s <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <=
              1048560i) **
       fact(8i + cm_rep_members_size (cm_function_params f) +
              cm_rep_members_size (cm_function_locals f) +
              8i * cm_stemps s <= 2147483647i) **
       fact(cm_temp_offset p fid (cm_stemps s) <=
              2147483647i) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_stmt_rep body s **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_emit_function p fid) tail`)]];
