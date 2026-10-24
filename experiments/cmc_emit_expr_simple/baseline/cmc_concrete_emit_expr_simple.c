#include "cmc_concrete_emit_expr_simple.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_emit_expr_dispatch.c"
#require "cmc_concrete_emit_expr_var.c"

void cm_emit_simple_expr(struct cm_program *program, int fid,
                         struct cm_function *fn, int pc, int temp,
                         struct cm_expr *expr, int lvalue,
                         struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `body:int`, `next:int`, `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_simple_expr e <=> true) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
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
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_expr_code_for p fid pc temp e lvalue ++ tail)`)]]
    [[cst::ensure(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_simple_expr e <=> true) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
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
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_expr_code_for p fid pc temp e lvalue) tail`)]]
{
  [[cst::proof]] { cm_open_expr_rep_st(); }
  if (expr->kind == CMC_EXPR_VAR) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_var_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 2i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`scope_:int`, `slot_:int`, `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMVarE (scope_:int) (slot_:int) (ty_:cm_type)`);
      cm_open_expr_count_facts(shape);
      cm_close_expr_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]][[cst::where(`fid`, `(fid__pre:int)`)]]
    cm_emit_var_expr(program, fid, fn, pc, temp, expr, lvalue, emitter);
  } else {
    [[cst::proof]] {
      thm simple = eqt_elim_rule(assume_rule(
          `cm_simple_expr (e:cm_expr) <=> true`));
      thm leaf = conv_rule(rewrite_conv(THM_LIST(
          cm_simple_expr_def,
          eqf_intro_rule(assume_rule(
            `~(cm_rep_expr_kind (e:cm_expr) == 2i)`)))), simple);
      add_fact_st(eqt_intro_rule(leaf));
      cm_close_expr_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]]
    cm_emit_leaf_expr(program, fid, fn, pc, temp, expr, lvalue, emitter);
  }
}
