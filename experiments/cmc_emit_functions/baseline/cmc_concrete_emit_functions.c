#include "cmc_concrete_emit_functions.h"
#include "cmc_concrete_emit_stmt_proof.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_emit_function.c"

PROOF static void cm_add_ready_facts(const thm theorem) {
  if (is_conj(concl(theorem))) {
    cm_add_ready_facts(conjunct1_rule(theorem));
    cm_add_ready_facts(conjunct2_rule(theorem));
    return;
  }
  term head = concl(theorem);
  while (is_comb(head)) {
    head = dest_comb(head).tm1;
  }
  bool encode = false;
  if (is_const(head)) {
    const char *name = dest_const(head).s;
    encode =
        strcmp(name, "cm_i32_code_count") == 0 ||
        strcmp(name, "cm_function_counts_representable") == 0 ||
        strcmp(name, "cm_stmt_wf") == 0 ||
        strcmp(name, "cm_stmt_counts_representable") == 0 ||
        strcmp(name, "cm_param_counts_representable") == 0 ||
        strcmp(name, "cm_slots_wf") == 0 ||
        strcmp(name, "cm_rep_members_safe") == 0 ||
        strcmp(name, "cm_rep_stmt_temps_safe") == 0 ||
        strcmp(name, "cm_concrete_functions_ready") == 0;
  }
  add_fact_st(encode ? eqt_intro_rule(theorem) : theorem);
}

void cmc_emit_functions(
    struct cm_program *program, struct cm_function *fn,
    int fid, int function_pc, struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `functions:(cm_function_d)list`,
                 `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(function_pc == cm_function_pc p fid) **
       fact(cm_concrete_functions_ready p fid functions <=> true) **
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
       cm_function_list_rep fn functions **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_emit_functions p fid functions ++ tail)`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(function_pc == cm_function_pc p fid) **
       fact(cm_concrete_functions_ready p fid functions <=> true) **
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
       cm_function_list_rep fn functions **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_emit_functions p fid functions) tail`)]]
{
  if (fn == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(TERM_LIST(
              `fn__pre:int`,
              `functions:(cm_function_d)list`),
              cm_function_list_null_shape),
            assume_rule(`fn__pre == 0i`))));
      thm nil_model = assume_rule(
          `functions == ([]:(cm_function_d)list)`);
      thm code_shape = by_rewrite(
          `cm_emit_functions (p:cm_program) (fid__pre:int)
             (functions:(cm_function_d)list) == []`,
          THM_LIST(nil_model, get_cm_emit_functions_def()));
      substitute_st(code_shape);
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
      substitute_st(sym_rule(ispec_rule(
          `done:(tvm_inst)list`, get_theorem_by_name("APPEND_NIL"))));
      thm prefix_shape = beta_norm(ap_term_rule(
          `\code:(tvm_inst)list. (done:(tvm_inst)list) ++ code`,
          sym_rule(code_shape)));
      substitute_st(prefix_shape);
    }
    return;
  };

  [[cst::proof]] {
    thm shape_open = mp_rule(specl_rule(TERM_LIST(
        `fn__pre:int`, `functions:(cm_function_d)list`),
        cm_function_list_nonnull_shape),
        assume_rule(`~(fn__pre == 0i)`));
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(shape_open,
          TERM_LIST(`f_:cm_function_d`,
            `rest_:(cm_function_d)list`))));
    thm shape = assume_rule(
        `functions == (f_:cm_function_d) ::
          (rest_:(cm_function_d)list)`);
    substitute_st(shape);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(specl_rule(TERM_LIST(
            `fn__pre:int`, `f_:cm_function_d`,
            `rest_:(cm_function_d)list`),
            cm_function_context_cons_open),
          TERM_LIST(`body_ptr_:int`, `next_ptr_:int`))));

    thm ready = conv_rule(rewrite_conv(THM_LIST(
        get_cm_concrete_functions_ready_def(),
        get_cm_concrete_function_ready_def())),
        from_state_bool(
          `cm_concrete_functions_ready (p:cm_program)
            (fid__pre:int)
            ((f_:cm_function_d) ::
              (rest_:(cm_function_d)list))`));
    cm_add_ready_facts(ready);
    cm_add_count_facts(ready);
  }

  int head_count = cmc_function_code_count(program, fid, fn);
  [[cst::proof]] {
    cm_retarget_stmt_call_result_st(
        `head_count__addr:addr`,
        assume_rule(
          `(retval:int) ==
           cm_function_code_count
             (p:cm_program) (fid__pre:int)`));
    thm code_shape = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_emit_functions_def(),
          get_theorem_by_name("APPEND"))),
        `cm_emit_functions (p:cm_program) (fid__pre:int)
          ((f_:cm_function_d) ::
            (rest_:(cm_function_d)list))`);
    cm_select_code_plan_st(code_shape);
    rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    thm pc_model = assume_rule(
        `(function_pc__pre:int) ==
         cm_function_pc (p:cm_program) (fid__pre:int)`);
    thm pc_i32 = conv_rule(rewrite_conv(THM_LIST(sym_rule(pc_model))),
        from_state_bool(
          `cm_i32_code_count
            (cm_function_pc (p:cm_program) (fid__pre:int))`));
    cm_add_count_facts(pc_i32);
    substitute_st(assume_rule(
        `(f_:cm_function_d) ==
         inth (fid__pre:int)
           (cm_program_functions (p:cm_program))`));
  }
  [[cst::where(
      `f`,
      `inth (fid:int) (cm_program_functions (p:cm_program))`)]]
  [[cst::where(
      `s`,
      `cm_function_body
        (inth (fid:int) (cm_program_functions (p:cm_program)))`)]]
  cmc_emit_function(program, fn, fid, function_pc, emitter);
  [[cst::proof]] {
    substitute_st(sym_rule(assume_rule(
        `(f_:cm_function_d) ==
         inth (fid__pre:int)
           (cm_program_functions (p:cm_program))`)));
  }

  struct cm_function *next_fn;
  [[cst::proof]] {
    thm function_view = apply_conversion(
        pure_rewrite_conv(THM_LIST(cm_function_context_rep_def)),
        `cm_function_context_rep (fn__pre:int)
          (f_:cm_function_d) (body_ptr_:int) (next_ptr_:int)`);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(eq2ent(function_view),
          TERM_LIST(`params_ptr_emit_:int`,
            `locals_ptr_emit_:int`))));
  }
  next_fn = fn->next;
  [[cst::proof]] {
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        cm_function_context_fold_hconv(
          `fn__pre:int`, `f_:cm_function_d`,
          `body_ptr_:int`, `next_ptr_:int`,
          `params_ptr_emit_:int`, `locals_ptr_emit_:int`)));
    thm step = assume_rule(
        `cm_function_pc (p:cm_program) ((fid__pre:int) + 1i) ==
         cm_function_pc p fid__pre +
           cm_function_code_count p fid__pre`);
    thm next_i32 = conv_rule(rewrite_conv(THM_LIST(step)),
        from_state_bool(
          `cm_i32_code_count
            (cm_function_pc (p:cm_program)
              ((fid__pre:int) + 1i))`));
    cm_add_count_facts(next_i32);
  }
  int next_pc = function_pc + head_count;
  [[cst::proof]] {
    thm pc_model = assume_rule(
        `(function_pc__pre:int) ==
         cm_function_pc (p:cm_program) (fid__pre:int)`);
    thm lifted = beta_norm(ap_term_rule(
        `\x:int. x + cm_function_code_count
          (p:cm_program) (fid__pre:int)`,
        pc_model));
    thm step = assume_rule(
        `cm_function_pc (p:cm_program) ((fid__pre:int) + 1i) ==
         cm_function_pc p fid__pre +
           cm_function_code_count p fid__pre`);
    add_fact_st(trans_rule(lifted, sym_rule(step)));
  }
  cmc_emit_functions(program, next_fn, fid + 1, next_pc, emitter);

  [[cst::proof]] {
    thm code_shape = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_emit_functions_def(),
          get_theorem_by_name("APPEND"))),
        `cm_emit_functions (p:cm_program) (fid__pre:int)
          ((f_:cm_function_d) ::
            (rest_:(cm_function_d)list))`);
    cm_restore_code_plan_st(code_shape);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        specl_rule(TERM_LIST(
            `fn__pre:int`, `f_:cm_function_d`,
            `rest_:(cm_function_d)list`,
            `body_ptr_:int`, `next_ptr_:int`),
            cm_function_context_cons_close)));
    substitute_st(sym_rule(assume_rule(
        `functions == (f_:cm_function_d) ::
          (rest_:(cm_function_d)list)`)));
  }
}
