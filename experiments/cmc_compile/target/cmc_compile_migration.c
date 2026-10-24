#include "cmc_layout_migration_abi.h"
#define CMC_OK 0
#define CMC_CAPACITY 1
struct cm_emitter { struct cm_output *output; int pc; };

/*@ Extern Coq
 (cm_struct_d :: *)
 (cm_global_d :: *)
 (cm_string_d :: *)
 (cm_function_d :: *)
 (cm_program :: *)
 (cm_lookup_policy :: *)
 (cm_codegen_obligations :: *)
 (tvm_inst :: *)
 (cm_source_lookup_policy :: *)
*/
/*@ Extern Coq
 (cm_struct_list_rep : Z -> list cm_struct_d -> Assertion)
 (cm_rep_structs_safe : list cm_struct_d -> Prop)
 (cm_global_list_rep : Z -> list cm_global_d -> Assertion)
 (cm_rep_globals_safe : list cm_global_d -> Prop)
 (cm_rep_globals_size : list cm_global_d -> Z)
 (cm_string_list_rep : Z -> list cm_string_d -> Assertion)
 (cm_rep_strings_safe : list cm_string_d -> Prop)
 (cm_rep_strings_size : list cm_string_d -> Z)
 (cm_program_globals : cm_program -> list cm_global_d)
 (cm_program_structs : cm_program -> list cm_struct_d)
 (cm_program_functions : cm_program -> list cm_function_d)
 (cm_program_strings : cm_program -> list cm_string_d)
 (cm_program_main : cm_program -> Z)
 (cm_wf_program : cm_lookup_policy -> cm_codegen_obligations -> cm_program -> Prop)
 (cm_i32_code_count : Z -> Prop)
 (cm_model_code_length : cm_lookup_policy -> cm_program -> Z)
 (cm_model_data_length : cm_program -> Z)
 (cm_model_data_bytes : cm_program -> list Z)
 (cm_program_context_rep : Z -> cm_program -> Z -> Assertion)
 (cm_function_list_rep : Z -> list cm_function_d -> Assertion)
 (cm_typed_program : cm_lookup_policy -> cm_program -> Prop)
 (cm_concrete_functions_ready : cm_lookup_policy -> cm_program -> Z -> list cm_function_d -> Prop)
 (cm_model_code : cm_lookup_policy -> cm_program -> list tvm_inst)
 (cm_resolved_emitter_plan_rep : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> list tvm_inst -> list tvm_inst -> Assertion)
 (cm_rep_ops : list tvm_inst -> list Z)
 (cm_rep_imms : list tvm_inst -> list Z)
 (cm_concrete_code_ready : cm_lookup_policy -> cm_program -> Prop)
 (cm_emitter_rep : Z -> Z -> Z -> list Z -> list Z -> Assertion)
 (cm_resolved_emitter_rep : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> list tvm_inst -> Assertion)
 (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
 (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
 (Int64Array::seg : Z -> Z -> Z -> list Z -> Assertion)
 (Int64Array::undef_seg : Z -> Z -> Z -> Assertion)
 (cm_data_globals_wf : list cm_struct_d -> list cm_global_d -> Prop)
 (cm_globals_bytes : list cm_struct_d -> list cm_global_d -> list Z)
 (cm_strings_bytes : list cm_string_d -> list Z)
 (UCharArray::seg : Z -> Z -> Z -> list Z -> Assertion)
 (UCharArray::undef_seg : Z -> Z -> Z -> Assertion)
 (zeros : Z -> list Z)
 (cm_source_function_policy : cm_source_lookup_policy -> cm_lookup_policy)
 (cm_source_codegen_obligations : cm_lookup_policy -> cm_codegen_obligations)
 (cm_semantic_wf_program : cm_lookup_policy -> cm_program -> Prop)
 (cm_program_rep : cm_lookup_policy -> Z -> cm_program -> Assertion)
 (cm_output_pre : Z -> Z -> Z -> Assertion)
 (cm_output_capacity : cm_lookup_policy -> Z -> Z -> Z -> cm_program -> Assertion)
 (cm_output_ok : cm_source_lookup_policy -> Z -> Z -> Z -> cm_program -> Assertion)
 (cm_undef_int_buffer : Z -> Z -> Assertion)
 (cm_undef_int64_buffer : Z -> Z -> Assertion)
 (cm_undef_uint8_buffer : Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_compile_migration_lib */

int cmc_model_code_length(struct cm_program *program)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (functions_ptr : Z)
    Require cm_wf_program(policy, cg, p) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p))
    Ensure cm_wf_program(policy, cg, p) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_model_code_length(policy, p) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p))
*/;

int cmc_model_data_length(struct cm_program *program)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (functions_ptr : Z)
    Require cm_wf_program(policy, cg, p) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_model_data_length(p) == 8 + cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) && cm_program_context_rep(program, p, functions_ptr)
    Ensure cm_wf_program(policy, cg, p) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_model_data_length(p) == 8 + cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) && __return == cm_model_data_length(p) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr)
*/;

void cmc_emit_code(struct cm_program *program,
                   struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && cm_concrete_functions_ready(policy, p, 0, cm_program_functions(p)) && cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p)) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_model_code(policy, p), tail))
 Ensure cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && cm_concrete_functions_ready(policy, p, 0, cm_program_functions(p)) && cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p)) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_model_code(policy, p)), tail)
*/;

void cmc_patch_resolved_calls(struct cm_program *program,
                              struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (resolved : list tvm_inst) (functions_ptr : Z) (out : Z) (capacity : Z)
    Require cm_wf_program(policy, cg, p) && cm_concrete_code_ready(policy, p) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p)) * cm_resolved_emitter_rep(policy, p, emitter, out, capacity, resolved)
    Ensure cm_wf_program(policy, cg, p) && cm_concrete_code_ready(policy, p) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p)) * cm_emitter_rep(emitter, out, capacity, cm_rep_ops(resolved), cm_rep_imms(resolved))
*/;

int cmc_emit_data(struct cm_global *global_node,
                  struct cm_string *string_node,
                  unsigned char *data, int capacity)
/*@ With (structs : list cm_struct_d) (globals : list cm_global_d)
         (strings : list cm_string_d)
    Require cm_rep_globals_safe(globals) && cm_data_globals_wf(structs, globals) &&
            cm_rep_strings_safe(strings) &&
            0 <= cm_rep_globals_size(globals) && 0 <= cm_rep_strings_size(strings) &&
            (8 + cm_rep_globals_size(globals)) + cm_rep_strings_size(strings) <= capacity &&
            capacity <= 2147483647 &&
            cm_global_list_rep(global_node, globals) *
            cm_string_list_rep(string_node, strings) *
            UCharArray::seg(data, 0, 0, nil) *
            UCharArray::undef_seg(data, 0, capacity)
    Ensure cm_rep_globals_safe(globals) && cm_data_globals_wf(structs, globals) &&
           cm_rep_strings_safe(strings) &&
           0 <= cm_rep_globals_size(globals) && 0 <= cm_rep_strings_size(strings) &&
           (8 + cm_rep_globals_size(globals)) + cm_rep_strings_size(strings) <= capacity &&
           capacity <= 2147483647 &&
           __return == (8 + cm_rep_globals_size(globals)) + cm_rep_strings_size(strings) &&
           cm_global_list_rep(global_node, globals) *
           cm_string_list_rep(string_node, strings) *
           UCharArray::seg(data, 0,
             (8 + cm_rep_globals_size(globals)) + cm_rep_strings_size(strings),
             app(app(zeros(8), cm_globals_bytes(structs, globals)), cm_strings_bytes(strings))) *
           UCharArray::undef_seg(data,
             (8 + cm_rep_globals_size(globals)) + cm_rep_strings_size(strings), capacity)
*/;
int cmc_compile(struct cm_program *program, struct cm_output *output)
/*@ With (sp : cm_source_lookup_policy) (p : cm_program) (code_capacity : Z) (data_capacity : Z)
 Require cm_program_rep(cm_source_function_policy(sp), program, p) * cm_output_pre(output, code_capacity, data_capacity)
 Ensure (__return == 0 && cm_program_rep(cm_source_function_policy(sp), program, p) * cm_output_ok(sp, output, code_capacity, data_capacity, p)) ||
        (__return == 1 && cm_program_rep(cm_source_function_policy(sp), program, p) * cm_output_capacity(cm_source_function_policy(sp), output, code_capacity, data_capacity, p))
*/
{
  /*@ Assert exists (functions_ptr : Z) (ops_ptr : Z) (imms_ptr : Z) (data_ptr : Z) (old_code : Z) (old_data : Z) (old_entry : Z),
    program == program@pre && output == output@pre && program != 0 && output != 0 &&
    cm_semantic_wf_program(cm_source_function_policy(sp), p) &&
    cm_wf_program(cm_source_function_policy(sp), cm_source_codegen_obligations(cm_source_function_policy(sp)), p) &&
    cm_typed_program(cm_source_function_policy(sp), p) && cm_concrete_code_ready(cm_source_function_policy(sp), p) &&
    cm_concrete_functions_ready(cm_source_function_policy(sp), p, 0, cm_program_functions(p)) &&
    cm_rep_structs_safe(cm_program_structs(p)) &&
    cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
    cm_data_globals_wf(cm_program_structs(p), cm_program_globals(p)) &&
    0 <= cm_rep_globals_size(cm_program_globals(p)) && 0 <= cm_rep_strings_size(cm_program_strings(p)) &&
    cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
    cm_model_data_length(p) == (8 + cm_rep_globals_size(cm_program_globals(p))) + cm_rep_strings_size(cm_program_strings(p)) &&
    0 <= code_capacity && code_capacity <= 2147483647 && 0 <= data_capacity && data_capacity <= 2147483647 &&
    cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p)) * data_at(&(output->ops), int *, ops_ptr) *
    data_at(&(output->imms), long long *, imms_ptr) *
    data_at(&(output->data), unsigned char *, data_ptr) *
    data_at(&(output->code_capacity), int, code_capacity) *
    data_at(&(output->data_capacity), int, data_capacity) *
    data_at(&(output->code_length), int, old_code) *
    data_at(&(output->data_length), int, old_data) *
    data_at(&(output->entry), int, old_entry) *
    cm_undef_int_buffer(ops_ptr, code_capacity) * cm_undef_int64_buffer(imms_ptr, code_capacity) * cm_undef_uint8_buffer(data_ptr, data_capacity)
  */
  int code_length = cmc_model_code_length(program) /*@ where policy = cm_source_function_policy(sp), cg = cm_source_codegen_obligations(cm_source_function_policy(sp)), p = p */;
  int data_length = cmc_model_data_length(program) /*@ where policy = cm_source_function_policy(sp), cg = cm_source_codegen_obligations(cm_source_function_policy(sp)), p = p */;
  output->code_length = code_length;
  output->data_length = data_length;
  output->entry = -1;
  if (code_length > output->code_capacity) {
    return CMC_CAPACITY;
  }
  if (data_length > output->data_capacity) {
    return CMC_CAPACITY;
  }
  /*@ Assert exists (functions_ptr : Z) (ops_ptr : Z) (imms_ptr : Z) (data_ptr : Z),
    program == program@pre && output == output@pre && program != 0 && output != 0 &&
    ops_ptr != 0 && imms_ptr != 0 && data_ptr != 0 &&
    code_length == cm_model_code_length(cm_source_function_policy(sp), p) && data_length == cm_model_data_length(p) &&
    0 <= code_length && code_length <= code_capacity && 0 <= data_length && data_length <= data_capacity &&
    cm_semantic_wf_program(cm_source_function_policy(sp), p) &&
    cm_wf_program(cm_source_function_policy(sp), cm_source_codegen_obligations(cm_source_function_policy(sp)), p) &&
    cm_typed_program(cm_source_function_policy(sp), p) && cm_concrete_code_ready(cm_source_function_policy(sp), p) &&
    cm_concrete_functions_ready(cm_source_function_policy(sp), p, 0, cm_program_functions(p)) &&
    cm_rep_structs_safe(cm_program_structs(p)) &&
    cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
    cm_data_globals_wf(cm_program_structs(p), cm_program_globals(p)) &&
    0 <= cm_rep_globals_size(cm_program_globals(p)) && 0 <= cm_rep_strings_size(cm_program_strings(p)) &&
    cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
    cm_model_data_length(p) == (8 + cm_rep_globals_size(cm_program_globals(p))) + cm_rep_strings_size(cm_program_strings(p)) &&
    0 <= code_capacity && code_capacity <= 2147483647 && 0 <= data_capacity && data_capacity <= 2147483647 &&
    cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p)) * data_at(&(output->ops), int *, ops_ptr) *
    data_at(&(output->imms), long long *, imms_ptr) *
    data_at(&(output->data), unsigned char *, data_ptr) *
    data_at(&(output->code_capacity), int, code_capacity) *
    data_at(&(output->data_capacity), int, data_capacity) *
    data_at(&(output->code_length), int, code_length) *
    data_at(&(output->data_length), int, data_length) *
    data_at(&(output->entry), int, -1) *
    IntArray::seg(ops_ptr, 0, 0, nil) * IntArray::undef_seg(ops_ptr, 0, code_capacity) * Int64Array::seg(imms_ptr, 0, 0, nil) * Int64Array::undef_seg(imms_ptr, 0, code_capacity) * UCharArray::seg(data_ptr, 0, 0, nil) * UCharArray::undef_seg(data_ptr, 0, data_capacity)
  */
  struct cm_emitter emitter;
  emitter.output = output;
  emitter.pc = 0;
  /*@ Assert exists (functions_ptr : Z) (data_ptr : Z),
    program == program@pre && output == output@pre && program != 0 && output != 0 && data_ptr != 0 &&
    code_length == cm_model_code_length(cm_source_function_policy(sp), p) && data_length == cm_model_data_length(p) &&
    0 <= code_length && code_length <= code_capacity && 0 <= data_length && data_length <= data_capacity &&
    cm_semantic_wf_program(cm_source_function_policy(sp), p) &&
    cm_wf_program(cm_source_function_policy(sp), cm_source_codegen_obligations(cm_source_function_policy(sp)), p) &&
    cm_typed_program(cm_source_function_policy(sp), p) && cm_concrete_code_ready(cm_source_function_policy(sp), p) &&
    cm_concrete_functions_ready(cm_source_function_policy(sp), p, 0, cm_program_functions(p)) &&
    cm_rep_structs_safe(cm_program_structs(p)) &&
    cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
    cm_data_globals_wf(cm_program_structs(p), cm_program_globals(p)) &&
    0 <= cm_rep_globals_size(cm_program_globals(p)) && 0 <= cm_rep_strings_size(cm_program_strings(p)) &&
    cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
    cm_model_data_length(p) == (8 + cm_rep_globals_size(cm_program_globals(p))) + cm_rep_strings_size(cm_program_strings(p)) &&
    0 <= code_capacity && code_capacity <= 2147483647 && 0 <= data_capacity && data_capacity <= 2147483647 &&
    cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p)) * data_at(&(output->data), unsigned char *, data_ptr) *
    data_at(&(output->data_capacity), int, data_capacity) *
    data_at(&(output->code_length), int, code_length) *
    data_at(&(output->data_length), int, data_length) *
    data_at(&(output->entry), int, -1) *
    UCharArray::seg(data_ptr, 0, 0, nil) * UCharArray::undef_seg(data_ptr, 0, data_capacity) *
    cm_resolved_emitter_plan_rep(cm_source_function_policy(sp), p, &emitter, output, code_capacity, nil, app(cm_model_code(cm_source_function_policy(sp), p), nil))
  */
  cmc_emit_code(program, &emitter) /*@ where policy = cm_source_function_policy(sp), cg = cm_source_codegen_obligations(cm_source_function_policy(sp)), p = p, out = output, capacity = code_capacity */;
  /*@ Assert exists (functions_ptr : Z) (data_ptr : Z),
    program == program@pre && output == output@pre && program != 0 && output != 0 && data_ptr != 0 &&
    code_length == cm_model_code_length(cm_source_function_policy(sp), p) && data_length == cm_model_data_length(p) &&
    0 <= code_length && code_length <= code_capacity && 0 <= data_length && data_length <= data_capacity &&
    cm_semantic_wf_program(cm_source_function_policy(sp), p) &&
    cm_wf_program(cm_source_function_policy(sp), cm_source_codegen_obligations(cm_source_function_policy(sp)), p) &&
    cm_typed_program(cm_source_function_policy(sp), p) && cm_concrete_code_ready(cm_source_function_policy(sp), p) &&
    cm_concrete_functions_ready(cm_source_function_policy(sp), p, 0, cm_program_functions(p)) &&
    cm_rep_structs_safe(cm_program_structs(p)) &&
    cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
    cm_data_globals_wf(cm_program_structs(p), cm_program_globals(p)) &&
    0 <= cm_rep_globals_size(cm_program_globals(p)) && 0 <= cm_rep_strings_size(cm_program_strings(p)) &&
    cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
    cm_model_data_length(p) == (8 + cm_rep_globals_size(cm_program_globals(p))) + cm_rep_strings_size(cm_program_strings(p)) &&
    0 <= code_capacity && code_capacity <= 2147483647 && 0 <= data_capacity && data_capacity <= 2147483647 &&
    cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p)) * data_at(&(output->data), unsigned char *, data_ptr) *
    data_at(&(output->data_capacity), int, data_capacity) *
    data_at(&(output->code_length), int, code_length) *
    data_at(&(output->data_length), int, data_length) *
    data_at(&(output->entry), int, -1) *
    UCharArray::seg(data_ptr, 0, 0, nil) * UCharArray::undef_seg(data_ptr, 0, data_capacity) *
    cm_resolved_emitter_rep(cm_source_function_policy(sp), p, &emitter, output, code_capacity, cm_model_code(cm_source_function_policy(sp), p))
  */

  cmc_patch_resolved_calls(program, &emitter) /*@ where policy = cm_source_function_policy(sp), cg = cm_source_codegen_obligations(cm_source_function_policy(sp)), p = p, resolved = cm_model_code(cm_source_function_policy(sp), p), out = output, capacity = code_capacity */;
  /*@ Assert exists (functions_ptr : Z) (structs_ptr : Z) (globals_ptr : Z) (strings_ptr : Z) (data_ptr : Z),
    program == program@pre && output == output@pre && program != 0 && output != 0 && data_ptr != 0 &&
    code_length == cm_model_code_length(cm_source_function_policy(sp), p) && data_length == cm_model_data_length(p) &&
    0 <= code_length && code_length <= code_capacity && 0 <= data_length && data_length <= data_capacity &&
    cm_semantic_wf_program(cm_source_function_policy(sp), p) &&
    cm_wf_program(cm_source_function_policy(sp), cm_source_codegen_obligations(cm_source_function_policy(sp)), p) &&
    cm_typed_program(cm_source_function_policy(sp), p) && cm_concrete_code_ready(cm_source_function_policy(sp), p) &&
    cm_concrete_functions_ready(cm_source_function_policy(sp), p, 0, cm_program_functions(p)) &&
    cm_rep_structs_safe(cm_program_structs(p)) &&
    cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
    cm_data_globals_wf(cm_program_structs(p), cm_program_globals(p)) &&
    0 <= cm_rep_globals_size(cm_program_globals(p)) && 0 <= cm_rep_strings_size(cm_program_strings(p)) &&
    cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
    cm_model_data_length(p) == (8 + cm_rep_globals_size(cm_program_globals(p))) + cm_rep_strings_size(cm_program_strings(p)) &&
    0 <= code_capacity && code_capacity <= 2147483647 && 0 <= data_capacity && data_capacity <= 2147483647 &&
    data_at(&(program->structs), struct cm_struct *, structs_ptr) *
    data_at(&(program->globals), struct cm_global *, globals_ptr) *
    data_at(&(program->strings), struct cm_string *, strings_ptr) *
    data_at(&(program->functions), struct cm_function *, functions_ptr) *
    data_at(&(program->main_id), int, cm_program_main(p)) *
    cm_struct_list_rep(structs_ptr, cm_program_structs(p)) *
    cm_global_list_rep(globals_ptr, cm_program_globals(p)) *
    cm_string_list_rep(strings_ptr, cm_program_strings(p)) *
    cm_function_list_rep(functions_ptr, cm_program_functions(p)) *
    data_at(&(output->data), unsigned char *, data_ptr) *
    data_at(&(output->data_capacity), int, data_capacity) *
    data_at(&(output->code_length), int, code_length) *
    data_at(&(output->data_length), int, data_length) *
    data_at(&(output->entry), int, -1) *
    UCharArray::seg(data_ptr, 0, 0, nil) * UCharArray::undef_seg(data_ptr, 0, data_capacity) *
    cm_emitter_rep(&emitter, output, code_capacity, cm_rep_ops(cm_model_code(cm_source_function_policy(sp), p)), cm_rep_imms(cm_model_code(cm_source_function_policy(sp), p)))
  */
  struct cm_global *globals = program->globals;
  struct cm_string *strings = program->strings;
  unsigned char *data = output->data;
  int output_data_capacity = output->data_capacity;
  int emitted_data = cmc_emit_data(
      globals, strings, data, output_data_capacity) /*@ where structs = cm_program_structs(p), globals = cm_program_globals(p), strings = cm_program_strings(p) */;
  /*@ Assert exists (functions_ptr : Z) (ops_ptr : Z) (imms_ptr : Z) (data_ptr : Z) (globals_ptr : Z) (strings_ptr : Z),
    program == program@pre && output == output@pre && program != 0 && output != 0 &&
    ops_ptr != 0 && imms_ptr != 0 && data_ptr != 0 &&
    code_length == cm_model_code_length(cm_source_function_policy(sp), p) && data_length == cm_model_data_length(p) &&
    0 <= code_length && code_length <= code_capacity && 0 <= data_length && data_length <= data_capacity &&
    cm_semantic_wf_program(cm_source_function_policy(sp), p) &&
    globals == globals_ptr && strings == strings_ptr &&
    data == data_ptr && output_data_capacity == data_capacity && emitted_data == data_length &&
    cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p)) * data_at(&(output->ops), int *, ops_ptr) *
    data_at(&(output->imms), long long *, imms_ptr) *
    data_at(&(output->data), unsigned char *, data_ptr) *
    data_at(&(output->code_capacity), int, code_capacity) *
    data_at(&(output->data_capacity), int, data_capacity) *
    data_at(&(output->code_length), int, code_length) *
    data_at(&(output->data_length), int, data_length) *
    data_at(&(output->entry), int, -1) *
    data_at(&(emitter.output), struct cm_output *, output) * data_at(&(emitter.pc), int, code_length) *
    IntArray::seg(ops_ptr, 0, code_length, cm_rep_ops(cm_model_code(cm_source_function_policy(sp), p))) * IntArray::undef_seg(ops_ptr, code_length, code_capacity) *
    Int64Array::seg(imms_ptr, 0, code_length, cm_rep_imms(cm_model_code(cm_source_function_policy(sp), p))) * Int64Array::undef_seg(imms_ptr, code_length, code_capacity) *
    UCharArray::seg(data_ptr, 0, data_length, cm_model_data_bytes(p)) * UCharArray::undef_seg(data_ptr, data_length, data_capacity)
  */
  output->entry = 0;
  return CMC_OK;
}
