#include "cmc_concrete_emit_expr_var.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_emit_ast.c"
#require "cmc_concrete_emit_plan.c"

PROOF static thm cm_var_code_shape(const thm shape,
                                   const thm lvalue_case,
                                   const thm array_case,
                                   const term code) {
  thm selected = by_rewrite(
      `cm_expr_code_for (p:cm_program) (fid__pre:int) (pc__pre:int)
         (temp__pre:int) (e:cm_expr) (lvalue__pre:int) ==
       (if lvalue__pre == 0i
        then cm_rcode_of
          (cm_emit_expr_pair p fid__pre pc__pre temp__pre e)
        else cm_lcode_of
          (cm_emit_expr_pair p fid__pre pc__pre temp__pre e))`,
      THM_LIST(cm_expr_code_for_def, lvalue_case,
        get_cm_emit_rvalue_def(), get_cm_emit_lvalue_def()));
  return trans_rule(selected, by_rewrite(
      mk_eq(rhs_of(selected), code), THM_LIST(
        shape, get_cm_emit_expr_pair_def(), get_cm_rcode_of_def(),
        get_cm_lcode_of_def(), lvalue_case, array_case,
        get_theorem_by_name("APPEND_NIL"))));
}


void cm_emit_var_expr(struct cm_program *program, int fid,
                      struct cm_function *fn, int pc, int temp,
                      struct cm_expr *expr, int lvalue,
                      struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `scope:int`, `slot:int`, `ty:cm_type`,
                 `body:int`, `next:int`, `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(e == CMVarE scope slot ty) **
       fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(0i <= slot) ** fact(slot <= 2147483647i) **
       fact(cm_binding_valid p f scope slot <=> true) **
       fact(cm_type_code_wf ty <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_expr_code_for p fid pc temp e lvalue ++ tail)`)]]
    [[cst::ensure(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(e == CMVarE scope slot ty) **
       fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(0i <= slot) ** fact(slot <= 2147483647i) **
       fact(cm_binding_valid p f scope slot <=> true) **
       fact(cm_type_code_wf ty <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_expr_code_for p fid pc temp e lvalue) tail`)]]
{
  [[cst::proof]] {
    cm_open_expr_rep_st();
    thm op_model = by_rewrite(
        `cm_rep_expr_op (e:cm_expr) == (scope:int)`,
        THM_LIST(assume_rule(
          `e == CMVarE (scope:int) (slot:int) (ty:cm_type)`),
          get_cm_rep_expr_op_def()));
    thm value_model = by_rewrite(
        `cm_rep_expr_value (e:cm_expr) == (slot:int)`,
        THM_LIST(assume_rule(
          `e == CMVarE (scope:int) (slot:int) (ty:cm_type)`),
          get_cm_rep_expr_value_def()));
    substitute_st(op_model);
    substitute_st(value_model);
    add_fact_st(mp_rule(mp_rule(spec_rule(`slot:int`,
        cm_nonnegative_i32_cast), assume_rule(`0i <= (slot:int)`)),
        assume_rule(`(slot:int) <= 2147483647i`)));
    cm_open_program_context_st();
    cm_open_function_context_st();
  }
  [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`globals`, `cm_program_globals (p:cm_program)`)]]
  [[cst::where(`locals`, `cm_function_locals (f:cm_function_d)`)]]
  int array = cmc_binding_array(program, fid, fn,
                                expr->op, (int)expr->value);
  [[cst::proof]] {
    cst_set_symbolic_state(retarget_cell_st(cst_get_symbolic_state(),
        `array__addr:addr`, `retval:int`,
        `cm_binding_array_code (p:cm_program) (fid__pre:int)
          (scope:int) (slot:int)`));
    cm_close_function_context_st();
    cm_close_program_context_st();
  }
  if (!lvalue) {
    if (array == 0) {
      [[cst::proof]] {
        thm not_array = eq_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `fid__pre:int`, `scope:int`, `slot:int`),
            cm_binding_array_code_zero), assume_rule(
              `cm_binding_array_code (p:cm_program) (fid__pre:int)
                (scope:int) (slot:int) == 0i`));
        thm code_shape = cm_var_code_shape(
            assume_rule(
              `e == CMVarE (scope:int) (slot:int) (ty:cm_type)`),
            eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
            eqf_intro_rule(not_array),
            `cm_binding_address_code p fid__pre scope slot ++
             cm_load_code (ty:cm_type)`);
        cm_select_code_plan_st(code_shape);
      }
      [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`f`, `(f:cm_function_d)`)]]
      [[cst::where(`fid`, `(fid__pre:int)`)]]
      [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
      [[cst::where(`globals`, `cm_program_globals (p:cm_program)`)]]
      cm_emit_binding_address_plan(program, fn, expr->op,
                                   (int)expr->value, emitter);
      [[cst::proof]] {
        add_fact_st(by_rewrite(
            `cm_type_encode (cm_expr_type (e:cm_expr)) ==
             cm_type_encode (ty:cm_type)`,
            THM_LIST(assume_rule(
              `e == CMVarE (scope:int) (slot:int) (ty:cm_type)`),
              get_cm_expr_type_def())));
      }
      [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`model_ty`, `(ty:cm_type)`)]]
      cm_emit_load_plan(emitter, expr->ty);
      [[cst::proof]] {
        thm not_array = eq_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `fid__pre:int`, `scope:int`, `slot:int`),
            cm_binding_array_code_zero), assume_rule(
              `cm_binding_array_code (p:cm_program) (fid__pre:int)
                (scope:int) (slot:int) == 0i`));
        thm code_shape = cm_var_code_shape(
            assume_rule(
              `e == CMVarE (scope:int) (slot:int) (ty:cm_type)`),
            eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
            eqf_intro_rule(not_array),
            `cm_binding_address_code p fid__pre scope slot ++
             cm_load_code (ty:cm_type)`);
        cm_restore_code_plan_st(code_shape);
      }
    } else {
      [[cst::proof]] {
        thm is_array = eq_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `fid__pre:int`, `scope:int`, `slot:int`),
            cm_binding_array_code_nonzero), assume_rule(
              `~(cm_binding_array_code (p:cm_program) (fid__pre:int)
                (scope:int) (slot:int) == 0i)`));
        thm code_shape = cm_var_code_shape(
            assume_rule(
              `e == CMVarE (scope:int) (slot:int) (ty:cm_type)`),
            eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
            eqt_intro_rule(is_array),
            `cm_binding_address_code p fid__pre scope slot`);
        cm_select_code_plan_st(code_shape);
      }
      [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`f`, `(f:cm_function_d)`)]]
      [[cst::where(`fid`, `(fid__pre:int)`)]]
      [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
      [[cst::where(`globals`, `cm_program_globals (p:cm_program)`)]]
      cm_emit_binding_address_plan(program, fn, expr->op,
                                   (int)expr->value, emitter);
      [[cst::proof]] {
        thm is_array = eq_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `fid__pre:int`, `scope:int`, `slot:int`),
            cm_binding_array_code_nonzero), assume_rule(
              `~(cm_binding_array_code (p:cm_program) (fid__pre:int)
                (scope:int) (slot:int) == 0i)`));
        thm code_shape = cm_var_code_shape(
            assume_rule(
              `e == CMVarE (scope:int) (slot:int) (ty:cm_type)`),
            eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
            eqt_intro_rule(is_array),
            `cm_binding_address_code p fid__pre scope slot`);
        cm_restore_code_plan_st(code_shape);
      }
    }
  } else {
    [[cst::proof]] {
      thm code_shape = cm_var_code_shape(
          assume_rule(
            `e == CMVarE (scope:int) (slot:int) (ty:cm_type)`),
          eqf_intro_rule(assume_rule(`~(lvalue__pre == 0i)`)),
          refl_rule(`T`),
          `cm_binding_address_code p fid__pre scope slot`);
      cm_select_code_plan_st(code_shape);
    }
    [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
    [[cst::where(`globals`, `cm_program_globals (p:cm_program)`)]]
    cm_emit_binding_address_plan(program, fn, expr->op,
                                 (int)expr->value, emitter);
    [[cst::proof]] {
      thm code_shape = cm_var_code_shape(
          assume_rule(
            `e == CMVarE (scope:int) (slot:int) (ty:cm_type)`),
          eqf_intro_rule(assume_rule(`~(lvalue__pre == 0i)`)),
          refl_rule(`T`),
          `cm_binding_address_code p fid__pre scope slot`);
      cm_restore_code_plan_st(code_shape);
    }
  }
  [[cst::proof]] {
    thm op_model = by_rewrite(
        `cm_rep_expr_op (e:cm_expr) == (scope:int)`,
        THM_LIST(assume_rule(
          `e == CMVarE (scope:int) (slot:int) (ty:cm_type)`),
          get_cm_rep_expr_op_def()));
    thm value_model = by_rewrite(
        `cm_rep_expr_value (e:cm_expr) == (slot:int)`,
        THM_LIST(assume_rule(
          `e == CMVarE (scope:int) (slot:int) (ty:cm_type)`),
          get_cm_rep_expr_value_def()));
    thm slot_lower = conv_rule(rewrite_conv(THM_LIST(value_model)),
        assume_rule(`0i <= cm_rep_expr_value (e:cm_expr)`));
    thm slot_upper = conv_rule(rewrite_conv(THM_LIST(value_model)),
        assume_rule(
          `cm_rep_expr_value (e:cm_expr) <= 2147483647i`));
    thm binding_valid = conv_rule(rewrite_conv(THM_LIST(
        op_model, value_model)), from_state_bool(
          `cm_binding_valid (p:cm_program) (f:cm_function_d)
            (cm_rep_expr_op (e:cm_expr))
            (cm_rep_expr_value e)`));
    substitute_st(sym_rule(value_model));
    substitute_st(sym_rule(op_model));
    add_fact_st(slot_lower);
    add_fact_st(slot_upper);
    add_fact_st(eqt_intro_rule(binding_valid));
    cm_close_expr_rep_st();
  }
}
