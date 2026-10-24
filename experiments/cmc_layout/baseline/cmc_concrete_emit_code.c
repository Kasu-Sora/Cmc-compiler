#include "cmc_concrete_emit_code.h"
#include "cmc_stack_local_syntax.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_emit_prelude.c"
#require "cmc_stack_local_syntax.c"

void cmc_emit_code(struct cm_program *program,
                   struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(cm_concrete_functions_ready p 0i
              (cm_program_functions p) <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe
              (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe
              (cm_program_strings p) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <=
              1048560i) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr
         (cm_program_functions p) **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_model_code p ++ tail)`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(cm_concrete_functions_ready p 0i
              (cm_program_functions p) <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe
              (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe
              (cm_program_strings p) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <=
              1048560i) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr
         (cm_program_functions p) **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_model_code p) tail`)]]
{
  struct cm_function *functions;
  [[cst::proof]] { cm_open_program_context_st(); }
  functions = program->functions;
  [[cst::proof]] {
    cm_close_program_context_st();
    thm code_shape = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_model_code_def(),
          get_theorem_by_name("APPEND"))),
        `cm_model_code (p:cm_program)`);
    cm_select_code_plan_st(code_shape);
    rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
  }
  cmc_emit_prelude(program, emitter);
  [[cst::proof]] {
    add_fact_st(sym_rule(ispec_rule(
        `p:cm_program`, cm_function_pc_zero)));
  }
  cmc_emit_functions(program, functions, 0, 11, emitter);
  [[cst::proof]] {
    thm code_shape = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_model_code_def(),
          get_theorem_by_name("APPEND"))),
        `cm_model_code (p:cm_program)`);
    cm_restore_code_plan_st(code_shape);
  }
}
