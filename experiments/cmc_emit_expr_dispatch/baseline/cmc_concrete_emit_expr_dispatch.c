#include "cmc_concrete_emit_expr_dispatch.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_emit_expr_leaf.c"

void cm_emit_leaf_expr(struct cm_program *program, int fid,
                       struct cm_function *fn, int pc, int temp,
                       struct cm_expr *expr, int lvalue,
                       struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `body:int`, `next:int`, `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_leaf_expr e <=> true) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_expr_code_for p fid pc temp e lvalue ++ tail)`)]]
    [[cst::ensure(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_leaf_expr e <=> true) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_expr_code_for p fid pc temp e lvalue) tail`)]]
{
  [[cst::proof]] { cm_open_expr_rep_st(); }
  if (expr->kind == CMC_EXPR_CONST) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_const_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 0i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`n_:int`, `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMConstE (n_:int) (ty_:cm_type)`);
      cm_open_expr_count_facts(shape);
      cm_close_expr_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]]
    cm_emit_const_expr(program, fid, fn, pc, temp, expr, lvalue, emitter);
  } else if (expr->kind == CMC_EXPR_STRING) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_string_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 1i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`sid_:int`, `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMStringE (sid_:int) (ty_:cm_type)`);
      cm_open_expr_count_facts(shape);
      cm_close_expr_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]]
    cm_emit_string_expr(program, fid, fn, pc, temp, expr, lvalue, emitter);
  } else if (expr->kind == CMC_EXPR_SIZEOF) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_sizeof_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 9i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`asked_:cm_type`, `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMSizeofE (asked_:cm_type) (ty_:cm_type)`);
      cm_open_expr_count_facts(shape);
      thm well_formed = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_expr_wf_def())),
          from_state_bool(
            `cm_expr_wf (p:cm_program) (f:cm_function_d) (e:cm_expr)`));
      add_fact_st(eqt_intro_rule(
          conjunct1_rule(conjunct2_rule(well_formed))));
      cm_close_expr_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]]
    cm_emit_sizeof_expr(program, fid, fn, pc, temp, expr, lvalue, emitter);
  } else {
    [[cst::proof]] {
      thm leaf = eqt_elim_rule(assume_rule(
          `cm_leaf_expr (e:cm_expr) <=> true`));
      thm is_getc = conv_rule(rewrite_conv(THM_LIST(
          cm_leaf_expr_def,
          eqf_intro_rule(assume_rule(
            `~(cm_rep_expr_kind (e:cm_expr) == 0i)`)),
          eqf_intro_rule(assume_rule(
            `~(cm_rep_expr_kind (e:cm_expr) == 1i)`)),
          eqf_intro_rule(assume_rule(
            `~(cm_rep_expr_kind (e:cm_expr) == 9i)`)))), leaf);
      add_fact_st(is_getc);
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_getc_shape_ent()), is_getc);
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`ty_:cm_type`))));
      thm shape = assume_rule(`e == CMGetcE (ty_:cm_type)`);
      cm_open_expr_count_facts(shape);
      cm_close_expr_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]]
    cm_emit_getc_expr(program, fid, fn, pc, temp, expr, lvalue, emitter);
  }
}
