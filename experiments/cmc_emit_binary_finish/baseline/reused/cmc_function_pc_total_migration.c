#include "cmc_layout_migration_abi.h"

/*@ Extern Coq
    (bool :: *) (cm_type :: *) (cm_stmt :: *) (cm_slot_d :: *)
    (cm_struct_d :: *) (cm_global_d :: *) (cm_string_d :: *)
    (cm_function_d :: *) (cm_program :: *) (cm_lookup_policy :: *)
    (cm_codegen_obligations :: *)
*/
/*@ Extern Coq
    (false : bool)
    (cm_type_encode : cm_type -> Z)
    (cm_function_ret : cm_function_d -> cm_type)
    (cm_function_params : cm_function_d -> list cm_slot_d)
    (cm_function_locals : cm_function_d -> list cm_slot_d)
    (cm_function_body : cm_function_d -> cm_stmt)
    (cm_program_structs : cm_program -> list cm_struct_d)
    (cm_program_globals : cm_program -> list cm_global_d)
    (cm_program_strings : cm_program -> list cm_string_d)
    (cm_program_functions : cm_program -> list cm_function_d)
    (cm_program_main : cm_program -> Z)
    (cm_wf_program : cm_lookup_policy -> cm_codegen_obligations -> cm_program -> Prop)
    (cm_rep_structs_safe : list cm_struct_d -> Prop)
    (cm_function_counts_representable : cm_lookup_policy -> cm_program -> Z -> cm_function_d -> Prop)
    (cm_functions_counts_representable : cm_lookup_policy -> cm_program -> list cm_function_d -> Z -> Prop)
    (cm_stmt_wf : cm_lookup_policy -> cm_program -> cm_function_d -> bool -> cm_stmt -> Prop)
    (cm_concrete_functions_ready : cm_lookup_policy -> cm_program -> Z -> list cm_function_d -> Prop)
    (cm_concrete_code_ready : cm_lookup_policy -> cm_program -> Prop)
    (cm_function_code_count : cm_lookup_policy -> cm_program -> Z -> Z)
    (cm_function_prefix : cm_lookup_policy -> cm_program -> list cm_function_d -> Z -> Z)
    (cm_function_pc : cm_lookup_policy -> cm_program -> Z -> Z)
    (cm_i32_code_count : Z -> Prop)
    (cm_program_context_rep : Z -> cm_program -> Z -> Assertion)
    (cm_function_context_rep : Z -> cm_function_d -> Z -> Z -> Assertion)
    (cm_function_list_rep : Z -> list cm_function_d -> Assertion)
    (cm_stmt_rep : Z -> cm_stmt -> Assertion)
    (cm_slot_list_rep : Z -> list cm_slot_d -> Assertion)
    (cm_struct_list_rep : Z -> list cm_struct_d -> Assertion)
    (cm_global_list_rep : Z -> list cm_global_d -> Assertion)
    (cm_string_list_rep : Z -> list cm_string_d -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_function_pc_total_migration_lib */

int cmc_function_code_count(struct cm_program *program, int fid,
                                   struct cm_function *fn)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (functions_ptr : Z) (body_ptr : Z) (next_ptr : Z)
    Require cm_wf_program(policy, cg, p) && cm_function_counts_representable(policy, p, fid, f) && cm_stmt_wf(policy, p, f, false, cm_function_body(f)) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body_ptr, next_ptr) * cm_stmt_rep(body_ptr, cm_function_body(f))
    Ensure cm_wf_program(policy, cg, p) && cm_function_counts_representable(policy, p, fid, f) && cm_stmt_wf(policy, p, f, false, cm_function_body(f)) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_function_code_count(policy, p, fid) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body_ptr, next_ptr) * cm_stmt_rep(body_ptr, cm_function_body(f))
*/
;

static int cmc_function_prefix_total(
    struct cm_program *program, struct cm_function *fn,
    int index, long long target)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (functions : list cm_function_d) (functions_ptr : Z)
    Require cm_wf_program(policy, cg, p) && cm_rep_structs_safe(cm_program_structs(p)) && 0 <= index && index == Zlength(cm_program_functions(p)) - Zlength(functions) && index + Zlength(functions) <= 2147483647 && cm_functions_counts_representable(policy, p, functions, index) && cm_concrete_functions_ready(policy, p, index, functions) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(fn, functions)
    Ensure cm_wf_program(policy, cg, p) && cm_rep_structs_safe(cm_program_structs(p)) && 0 <= index && index == Zlength(cm_program_functions(p)) - Zlength(functions) && index + Zlength(functions) <= 2147483647 && cm_functions_counts_representable(policy, p, functions, index) && cm_concrete_functions_ready(policy, p, index, functions) && __return == cm_function_prefix(policy, p, functions, target - index) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(fn, functions)
*/
{
  if (fn == 0) {
    return 0;
  };
  if (index == target) {
    return 0;
  };
  /*@ Assert exists (f : cm_function_d) (rest : list cm_function_d) (bp : Z) (np : Z),
    program == program@pre && fn == fn@pre && index == index@pre && target == target@pre &&
    fn != 0 && index != target &&
    functions == cons(f, rest) &&
    cm_function_counts_representable(policy, p, index, f) &&
    cm_stmt_wf(policy, p, f, false, cm_function_body(f)) &&
    cm_functions_counts_representable(policy, p, rest, index + 1) &&
    cm_concrete_functions_ready(policy, p, index + 1, rest) &&
    cm_i32_code_count(index + 1) &&
    cm_wf_program(policy, cg, p) && cm_rep_structs_safe(cm_program_structs(p)) && 0 <= index && index == Zlength(cm_program_functions(p)) - Zlength(functions) && index + Zlength(functions) <= 2147483647 && cm_functions_counts_representable(policy, p, functions, index) && cm_concrete_functions_ready(policy, p, index, functions) &&
    cm_program_context_rep(program, p, functions_ptr) *
    cm_function_context_rep(fn, f, bp, np) *
    cm_stmt_rep(bp, cm_function_body(f)) *
    cm_function_list_rep(np, rest)
  */
  int head_count = cmc_function_code_count(program, index, fn) /*@ where policy = policy, cg = cg, p = p, functions_ptr = functions_ptr */;
  /*@ Assert exists (f : cm_function_d) (rest : list cm_function_d) (bp : Z) (np : Z) (pp : Z) (lp : Z),
    program == program@pre && fn == fn@pre && index == index@pre && target == target@pre &&
    fn != 0 && index != target &&
    functions == cons(f, rest) &&
    cm_function_counts_representable(policy, p, index, f) &&
    cm_stmt_wf(policy, p, f, false, cm_function_body(f)) &&
    cm_functions_counts_representable(policy, p, rest, index + 1) &&
    cm_concrete_functions_ready(policy, p, index + 1, rest) &&
    cm_i32_code_count(index + 1) &&
    cm_wf_program(policy, cg, p) && cm_rep_structs_safe(cm_program_structs(p)) && 0 <= index && index == Zlength(cm_program_functions(p)) - Zlength(functions) && index + Zlength(functions) <= 2147483647 && cm_functions_counts_representable(policy, p, functions, index) && cm_concrete_functions_ready(policy, p, index, functions) &&
    head_count == cm_function_code_count(policy, p, index) && cm_i32_code_count(head_count) &&
    cm_program_context_rep(program, p, functions_ptr) *
    data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) *
    data_at(&(fn->params), struct cm_slot *, pp) *
    data_at(&(fn->locals), struct cm_slot *, lp) *
    data_at(&(fn->body), struct cm_stmt *, bp) *
    data_at(&(fn->next), struct cm_function *, np) *
    cm_slot_list_rep(pp, cm_function_params(f)) *
    cm_slot_list_rep(lp, cm_function_locals(f)) *
    cm_stmt_rep(bp, cm_function_body(f)) *
    cm_function_list_rep(np, rest)
  */
  struct cm_function *next_fn;
  next_fn = fn->next;
  int tail_count = cmc_function_prefix_total(
      program, next_fn, index + 1, target) /*@ where policy = policy, cg = cg, p = p, functions_ptr = functions_ptr */;
  int result = head_count + tail_count;
  return result;
}

int cmc_function_pc_total(struct cm_program *program, long long target)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (functions_ptr : Z)
    Require cm_wf_program(policy, cg, p) && cm_concrete_code_ready(policy, p) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p))
    Ensure cm_wf_program(policy, cg, p) && cm_concrete_code_ready(policy, p) && __return == cm_function_pc(policy, p, target) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p))
*/
{
  /*@ Assert exists (sp : Z) (gp : Z) (tp : Z),
    program == program@pre && target == target@pre && program != 0 &&
    cm_wf_program(policy, cg, p) && cm_concrete_code_ready(policy, p) &&
    cm_rep_structs_safe(cm_program_structs(p)) &&
    Zlength(cm_program_functions(p)) <= 2147483647 &&
    cm_functions_counts_representable(policy, p, cm_program_functions(p), 0) &&
    cm_concrete_functions_ready(policy, p, 0, cm_program_functions(p)) &&
    data_at(&(program->structs), struct cm_struct *, sp) *
    data_at(&(program->globals), struct cm_global *, gp) *
    data_at(&(program->strings), struct cm_string *, tp) *
    data_at(&(program->functions), struct cm_function *, functions_ptr) *
    data_at(&(program->main_id), int, cm_program_main(p)) *
    cm_struct_list_rep(sp, cm_program_structs(p)) *
    cm_global_list_rep(gp, cm_program_globals(p)) *
    cm_string_list_rep(tp, cm_program_strings(p)) *
    cm_function_list_rep(functions_ptr, cm_program_functions(p))
  */
  struct cm_function *fn = program->functions;
  /*@ Assert program == program@pre && target == target@pre &&
    program != 0 && fn == functions_ptr &&
    cm_wf_program(policy, cg, p) && cm_concrete_code_ready(policy, p) &&
    cm_rep_structs_safe(cm_program_structs(p)) &&
    Zlength(cm_program_functions(p)) <= 2147483647 &&
    cm_functions_counts_representable(policy, p, cm_program_functions(p), 0) &&
    cm_concrete_functions_ready(policy, p, 0, cm_program_functions(p)) &&
    cm_program_context_rep(program, p, functions_ptr) *
    cm_function_list_rep(functions_ptr, cm_program_functions(p))
  */
  int prefix = cmc_function_prefix_total(program, fn, 0, target) /*@ where policy = policy, cg = cg, p = p, functions_ptr = functions_ptr, functions = cm_program_functions(p) */;
  int result = 11 + prefix;
  return result;
}
