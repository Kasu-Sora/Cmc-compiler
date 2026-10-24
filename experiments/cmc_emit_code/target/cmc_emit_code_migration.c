#include "cmc_layout_migration_abi.h"

struct cm_emitter {
  struct cm_output *output;
  int pc;
};

/*@ Extern Coq
 (cm_program :: *) (cm_lookup_policy :: *) (cm_codegen_obligations :: *)
 (tvm_inst :: *) (cm_function_d :: *) (cm_struct_d :: *) (cm_global_d :: *) (cm_string_d :: *)
*/
/*@ Extern Coq
 (cm_program_main : cm_program -> Z)
 (cm_program_structs : cm_program -> list cm_struct_d)
 (cm_program_globals : cm_program -> list cm_global_d)
 (cm_program_strings : cm_program -> list cm_string_d)
 (cm_program_functions : cm_program -> list cm_function_d)
 (cm_struct_list_rep : Z -> list cm_struct_d -> Assertion)
 (cm_global_list_rep : Z -> list cm_global_d -> Assertion)
 (cm_string_list_rep : Z -> list cm_string_d -> Assertion)
 (cm_program_context_rep : Z -> cm_program -> Z -> Assertion)
 (cm_function_list_rep : Z -> list cm_function_d -> Assertion)
 (cm_wf_program : cm_lookup_policy -> cm_codegen_obligations -> cm_program -> Prop)
 (cm_typed_program : cm_lookup_policy -> cm_program -> Prop)
 (cm_concrete_functions_ready : cm_lookup_policy -> cm_program -> Z -> list cm_function_d -> Prop)
 (cm_rep_structs_safe : list cm_struct_d -> Prop)
 (cm_rep_globals_safe : list cm_global_d -> Prop)
 (cm_rep_strings_safe : list cm_string_d -> Prop)
 (cm_rep_globals_size : list cm_global_d -> Z)
 (cm_rep_strings_size : list cm_string_d -> Z)
 (cm_function_pc : cm_lookup_policy -> cm_program -> Z -> Z)
 (cm_emit_prelude : cm_lookup_policy -> cm_program -> list tvm_inst)
 (cm_emit_functions : cm_lookup_policy -> cm_program -> Z -> list cm_function_d -> list tvm_inst)
 (cm_model_code : cm_lookup_policy -> cm_program -> list tvm_inst)
 (cm_resolved_emitter_plan_rep : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> list tvm_inst -> list tvm_inst -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_emit_code_migration_lib */

void cmc_emit_prelude(struct cm_program *program,
                      struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require cm_program_context_rep(program, p, functions_ptr) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_prelude(policy, p), tail))
 Ensure cm_program_context_rep(program, p, functions_ptr) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_prelude(policy, p)), tail)
*/;

void cmc_emit_functions(
    struct cm_program *program, struct cm_function *fn,
    int fid, int function_pc, struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (functions : list cm_function_d) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && function_pc == cm_function_pc(policy, p, fid) && cm_concrete_functions_ready(policy, p, fid, functions) && cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(fn, functions) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_functions(policy, p, fid, functions), tail))
 Ensure cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && function_pc == cm_function_pc(policy, p, fid) && cm_concrete_functions_ready(policy, p, fid, functions) && cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(fn, functions) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_functions(policy, p, fid, functions)), tail)
*/;

void cmc_emit_code(struct cm_program *program,
                   struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && cm_concrete_functions_ready(policy, p, 0, cm_program_functions(p)) && cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p)) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_model_code(policy, p), tail))
 Ensure cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && cm_concrete_functions_ready(policy, p, 0, cm_program_functions(p)) && cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p)) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_model_code(policy, p)), tail)
*/
{
  struct cm_function *functions;
  /*@ Assert exists (sp : Z) (gp : Z) (tp : Z),
    program == program@pre && emitter == emitter@pre && program != 0 &&
    cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && cm_concrete_functions_ready(policy, p, 0, cm_program_functions(p)) && cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
    undef_data_at(&functions, struct cm_function *) *
    data_at(&(program->structs), struct cm_struct *, sp) *
    data_at(&(program->globals), struct cm_global *, gp) *
    data_at(&(program->strings), struct cm_string *, tp) *
    data_at(&(program->functions), struct cm_function *, functions_ptr) *
    data_at(&(program->main_id), int, cm_program_main(p)) *
    cm_struct_list_rep(sp, cm_program_structs(p)) *
    cm_global_list_rep(gp, cm_program_globals(p)) *
    cm_string_list_rep(tp, cm_program_strings(p)) *
    cm_function_list_rep(functions_ptr, cm_program_functions(p)) *
    cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_model_code(policy, p), tail))
  */
  functions = program->functions;
  /*@ Assert program == program@pre && emitter == emitter@pre && functions == functions_ptr &&
    cm_function_pc(policy, p, 0) == 11 &&
    cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && cm_concrete_functions_ready(policy, p, 0, cm_program_functions(p)) && cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
    cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p)) *
    cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_prelude(policy, p), app(cm_emit_functions(policy, p, 0, cm_program_functions(p)), tail)))
  */
  cmc_emit_prelude(program, emitter) /*@ where policy = policy, p = p, functions_ptr = functions_ptr, done = done, tail = app(cm_emit_functions(policy, p, 0, cm_program_functions(p)), tail), out = out, capacity = capacity */;
  cmc_emit_functions(program, functions, 0, 11, emitter) /*@ where policy = policy, cg = cg, p = p, functions = cm_program_functions(p), functions_ptr = functions_ptr, done = app(done, cm_emit_prelude(policy, p)), tail = tail, out = out, capacity = capacity */;
}
