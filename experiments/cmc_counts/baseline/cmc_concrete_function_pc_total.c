#include "cmc_concrete_function_pc_total.h"
#include "cmc_stack_local_syntax.h"
#require "cmc_stack_local_syntax.c"
#require "cmc_concrete_compile_ready.c"

PROOF static thm cm_total_join_facts(const thm_list facts) {
  size_t count = vector_size(facts);
  if (count == 0) abort();
  thm result = facts[count - 1];
  for (size_t i = count - 1; i > 0; --i) {
    result = conj_rule(facts[i - 1], result);
  }
  return result;
}

PROOF static thm cm_total_i32_from_bounds(
    const term value, const thm bounds) {
  thm view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_i32_code_count_def())),
      mk_comb(`cm_i32_code_count:int->bool`, value));
  return eq_mp_rule(sym_rule(view), bounds);
}


PROOF static thm cm_prove_function_prefix_total_bounds(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list). !(p:cm_program) remaining.
         0i <= cm_function_prefix p functions remaining &&
         cm_function_prefix p functions remaining <=
           cm_functions_code_size p functions
             (ilength (cm_program_functions p) - ilength functions)`);
  gnode_list cases = INDUCT_TAC(root,
      `functions:(cm_function_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_function_prefix_def(),
        get_cm_functions_code_size_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm induction = assume_rule(
        `!(p:cm_program) remaining.
           0i <= cm_function_prefix p
             (a1:(cm_function_d)list) remaining &&
           cm_function_prefix p a1 remaining <=
             cm_functions_code_size p a1
               (ilength (cm_program_functions p) - ilength a1)`);
    gnode_list branches = BOOL_CASES_TAC(
        leaf, `(remaining:int) == 0i`, "hremaining");
    {
      thm head_nonnegative = specl_rule(TERM_LIST(
          `p:cm_program`,
          `ilength (cm_program_functions (p:cm_program)) -
            ilength ((a0:cm_function_d) ::
              (a1:(cm_function_d)list))`),
          cm_function_code_count_nonnegative);
      thm tail_nonnegative = specl_rule(TERM_LIST(
          `a1:(cm_function_d)list`, `p:cm_program`,
          `ilength (cm_program_functions (p:cm_program)) -
            ilength ((a0:cm_function_d) ::
              (a1:(cm_function_d)list)) + 1i`),
          cm_functions_code_size_nonnegative);
      gnode reduced = CONV_TAC(
          branches[0], reduce_rewrite_conv(THM_LIST(
            assume_rule(`(remaining:int) == 0i`),
            get_cm_function_prefix_def(),
            get_cm_functions_code_size_def(),
            get_theorem_by_name("ILENGTH_DEF"))));
      if (IS_NULL(reduced->solved)) {
        thm facts = conj_rule(head_nonnegative, tail_nonnegative);
        thm cons_length = apply_conversion(rewrite_conv(THM_LIST(
            get_theorem_by_name("ILENGTH_DEF"))),
            `ilength ((a0:cm_function_d) ::
              (a1:(cm_function_d)list))`);
        thm normalized_facts = conv_rule(rewrite_conv(THM_LIST(
            cons_length)), facts);
        ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
            concl(normalized_facts), goal_ccl(reduced->g))),
            normalized_facts));
      }
    }
    {
      thm tail_bounds = specl_rule(TERM_LIST(
          `p:cm_program`, `(remaining:int) - 1i`), induction);
      thm head_nonnegative = specl_rule(TERM_LIST(
          `p:cm_program`,
          `ilength (cm_program_functions (p:cm_program)) -
            ilength ((a0:cm_function_d) ::
              (a1:(cm_function_d)list))`),
          cm_function_code_count_nonnegative);
      gnode reduced = CONV_WITH_ASMP_TAC(
          branches[1], reduce_rewrite_conv, THM_LIST(
            get_cm_function_prefix_def(),
            get_cm_functions_code_size_def(),
            get_theorem_by_name("ILENGTH_DEF")));
      if (IS_NULL(reduced->solved)) {
        thm cons_length = apply_conversion(rewrite_conv(THM_LIST(
            get_theorem_by_name("ILENGTH_DEF"))),
            `ilength ((a0:cm_function_d) ::
              (a1:(cm_function_d)list))`);
        thm tail_index = int_arith_rule(
            `ilength (cm_program_functions (p:cm_program)) -
               ilength (a1:(cm_function_d)list) ==
             ilength (cm_program_functions p) -
               (1i + ilength a1) + 1i`);
        thm normalized_head = conv_rule(rewrite_conv(THM_LIST(
            cons_length)), head_nonnegative);
        thm normalized_tail = conv_rule(once_rewrite_conv(THM_LIST(
            tail_index)), tail_bounds);
        thm facts = conj_rule(normalized_tail, normalized_head);
        ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
            concl(facts), goal_ccl(reduced->g))), facts));
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_function_prefix_total_bounds =
    cm_prove_function_prefix_total_bounds();

PROOF static void cm_add_total_ready_facts(const thm theorem) {
  if (is_conj(concl(theorem))) {
    cm_add_total_ready_facts(conjunct1_rule(theorem));
    cm_add_total_ready_facts(conjunct2_rule(theorem));
    return;
  }
  term head = concl(theorem);
  while (is_comb(head)) head = dest_comb(head).tm1;
  bool encode = false;
  if (is_const(head)) {
    const char *name = dest_const(head).s;
    encode =
        strcmp(name, "cm_i32_code_count") == 0 ||
        strcmp(name, "cm_function_counts_representable") == 0 ||
        strcmp(name, "cm_functions_counts_representable") == 0 ||
        strcmp(name, "cm_stmt_wf") == 0 ||
        strcmp(name, "cm_stmt_counts_representable") == 0 ||
        strcmp(name, "cm_param_counts_representable") == 0 ||
        strcmp(name, "cm_slots_wf") == 0 ||
        strcmp(name, "cm_rep_members_safe") == 0 ||
        strcmp(name, "cm_rep_stmt_temps_safe") == 0 ||
        strcmp(name, "cm_concrete_function_ready") == 0 ||
        strcmp(name, "cm_concrete_functions_ready") == 0;
  }
  add_fact_st(encode ? eqt_intro_rule(theorem) : theorem);
}

static int cmc_function_prefix_total(
    struct cm_program *program, struct cm_function *fn,
    int index, long long target)
    [[cst::param(`p:cm_program`, `functions:(cm_function_d)list`,
                 `functions_ptr:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(0i <= index) **
       fact(index == ilength (cm_program_functions p) -
                       ilength functions) **
       fact(index + ilength functions <= 2147483647i) **
       fact(cm_functions_counts_representable
              p functions index <=> true) **
       fact(cm_concrete_functions_ready p index functions <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep fn functions`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(0i <= index) **
       fact(index == ilength (cm_program_functions p) -
                       ilength functions) **
       fact(index + ilength functions <= 2147483647i) **
       fact(cm_functions_counts_representable
              p functions index <=> true) **
       fact(cm_concrete_functions_ready p index functions <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep fn functions **
       fact((__return:int) ==
         cm_function_prefix p functions (target - index)) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]]
{
  if (fn == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(TERM_LIST(
              `fn__pre:int`, `functions:(cm_function_d)list`),
              cm_function_list_null_shape),
            assume_rule(`fn__pre == 0i`))));
      thm nil_model = assume_rule(
          `functions == ([]:(cm_function_d)list)`);
      add_fact_st(by_rewrite(
          `cm_function_prefix (p:cm_program)
             (functions:(cm_function_d)list)
             ((target__pre:int) - (index__pre:int)) == 0i`,
          THM_LIST(nil_model, get_cm_function_prefix_def())));
      add_fact_st(eqt_intro_rule(eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
          `cm_i32_code_count 0i`))));
    }
    return 0;
  };

  if (index == target) {
    [[cst::proof]] {
      thm remaining_zero = mp_rule(int_arith_rule(
          `(index__pre:int) == (target__pre:int) ==>
           target__pre - index__pre == 0i`),
          assume_rule(`(index__pre:int) == (target__pre:int)`));
      add_fact_st(by_rewrite(
          `cm_function_prefix (p:cm_program)
             (functions:(cm_function_d)list)
             ((target__pre:int) - (index__pre:int)) == 0i`,
          THM_LIST(remaining_zero, cm_function_prefix_zero)));
      add_fact_st(eqt_intro_rule(eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
          `cm_i32_code_count 0i`))));
    }
    return 0;
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
            (index__pre:int)
            ((f_:cm_function_d) ::
              (rest_:(cm_function_d)list))`));
    cm_add_total_ready_facts(ready);
    cm_add_count_facts(ready);
    thm counts = conv_rule(rewrite_conv(THM_LIST(
        get_cm_functions_counts_representable_def())),
        from_state_bool(
          `cm_functions_counts_representable (p:cm_program)
            ((f_:cm_function_d) ::
              (rest_:(cm_function_d)list))
            (index__pre:int)`));
    cm_add_total_ready_facts(counts);
    cm_add_count_facts(counts);
    thm function_at = assume_rule(
        `(f_:cm_function_d) ==
         inth (index__pre:int)
           (cm_program_functions (p:cm_program))`);
    thm alignment = assume_rule(
        `(index__pre:int) ==
         ilength (cm_program_functions (p:cm_program)) -
           ilength ((f_:cm_function_d) ::
             (rest_:(cm_function_d)list))`);
    thm call_index = conv_rule(once_rewrite_conv(THM_LIST(
        function_at)), alignment);
    thm call_counts = conv_rule(once_rewrite_conv(THM_LIST(
        call_index)), from_state_bool(
          `cm_function_counts_representable (p:cm_program)
            (index__pre:int) (f_:cm_function_d)`));
    add_fact_st(eqt_intro_rule(call_counts));
  }

  int head_count = cmc_function_code_count(program, index, fn);
  [[cst::proof]] {
    thm return_model = assume_rule(
        `(retval:int) ==
         cm_function_code_count (p:cm_program) (index__pre:int)`);
    add_fact_st(return_model);
    cst_set_symbolic_state(retarget_cell_st(
        cst_get_symbolic_state(), `head_count__addr:addr`,
        `retval:int`,
        `cm_function_code_count (p:cm_program) (index__pre:int)`));
    cm_add_count_facts(conv_rule(rewrite_conv(THM_LIST(return_model)),
        from_state_bool(`cm_i32_code_count (retval:int)`)));
  }

  struct cm_function *next_fn;
  [[cst::proof]] {
    thm function_view = apply_conversion(
        pure_rewrite_conv(THM_LIST(cm_function_context_rep_def)),
        `cm_function_context_rep (fn__pre:int)
          (f_:cm_function_d) (body_ptr_:int) (next_ptr_:int)`);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(eq2ent(function_view),
          TERM_LIST(`params_ptr_total_:int`,
            `locals_ptr_total_:int`))));
  }
  next_fn = fn->next;
  [[cst::proof]] {
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        cm_function_context_fold_hconv(
          `fn__pre:int`, `f_:cm_function_d`,
          `body_ptr_:int`, `next_ptr_:int`,
          `params_ptr_total_:int`, `locals_ptr_total_:int`)));
    cm_commit_arith_fact(
        "0i <= (index__pre:int) ==> 0i <= index__pre + 1i");
    thm id_i32 = from_state_bool(
        `cm_i32_code_count ((index__pre:int) + 1i)`);
    cm_add_count_facts(id_i32);
    thm cons_length = apply_conversion(rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ((f_:cm_function_d) ::
          (rest_:(cm_function_d)list))`);
    thm alignment = assume_rule(
        `(index__pre:int) ==
         ilength (cm_program_functions (p:cm_program)) -
           ilength ((f_:cm_function_d) ::
             (rest_:(cm_function_d)list))`);
    thm tail_alignment = mp_rule(int_arith_rule(mk_imp(
        concl(conj_rule(alignment, cons_length)),
        `(index__pre:int) + 1i ==
         ilength (cm_program_functions (p:cm_program)) -
           ilength (rest_:(cm_function_d)list)`)),
        conj_rule(alignment, cons_length));
    add_fact_st(tail_alignment);
    thm full_bound = assume_rule(
        `(index__pre:int) +
          ilength ((f_:cm_function_d) ::
            (rest_:(cm_function_d)list)) <= 2147483647i`);
    thm tail_bound_facts = conj_rule(full_bound, cons_length);
    add_fact_st(mp_rule(int_arith_rule(mk_imp(
        concl(tail_bound_facts),
        `((index__pre:int) + 1i) +
          ilength (rest_:(cm_function_d)list) <= 2147483647i`)),
        tail_bound_facts));
  }

  int tail_count = cmc_function_prefix_total(
      program, next_fn, index + 1, target);
  [[cst::proof]] {
    thm tail_model = assume_rule(
        `(retval_1:int) ==
         cm_function_prefix (p:cm_program)
           (rest_:(cm_function_d)list)
           ((target__pre:int) - ((index__pre:int) + 1i))`);
    add_fact_st(tail_model);
    cst_set_symbolic_state(retarget_cell_st(
        cst_get_symbolic_state(), `tail_count__addr:addr`,
        `retval_1:int`,
        `cm_function_prefix (p:cm_program)
          (rest_:(cm_function_d)list)
          ((target__pre:int) - ((index__pre:int) + 1i))`));
    cm_add_count_facts(conv_rule(rewrite_conv(THM_LIST(tail_model)),
        from_state_bool(`cm_i32_code_count (retval_1:int)`)));

    thm remaining_nonzero = mp_rule(int_arith_rule(
        `~((index__pre:int) == (target__pre:int)) ==>
         ~(((target__pre:int) - index__pre) == 0i)`),
        assume_rule(`~((index__pre:int) == (target__pre:int))`));
    thm remaining_step = int_arith_rule(
        `((target__pre:int) - (index__pre + 1i)) ==
         (target__pre - index__pre) - 1i`);
    thm prefix_model = by_rewrite(
        `cm_function_code_count (p:cm_program) (index__pre:int) +
           cm_function_prefix p (rest_:(cm_function_d)list)
             (target__pre - (index__pre + 1i)) ==
         cm_function_prefix p
           ((f_:cm_function_d) :: rest_)
           (target__pre - index__pre)`,
        THM_LIST(get_cm_function_prefix_def(),
          get_theorem_by_name("ILENGTH_DEF"),
          remaining_nonzero, remaining_step,
          assume_rule(
            `(index__pre:int) ==
             ilength (cm_program_functions (p:cm_program)) -
               ilength ((f_:cm_function_d) ::
                 (rest_:(cm_function_d)list))`)));
    add_fact_st(prefix_model);

    thm prefix_bounds = specl_rule(TERM_LIST(
        `(f_:cm_function_d) :: (rest_:(cm_function_d)list)`,
        `p:cm_program`, `(target__pre:int) - (index__pre:int)`),
        cm_function_prefix_total_bounds);
    thm size_i32 = conv_rule(rewrite_conv(THM_LIST(
        get_cm_i32_code_count_def())),
        from_state_bool(
          `cm_i32_code_count
            (cm_functions_code_size (p:cm_program)
              ((f_:cm_function_d) ::
                (rest_:(cm_function_d)list))
              (index__pre:int))`));
    thm size_index = sym_rule(assume_rule(
        `(index__pre:int) ==
         ilength (cm_program_functions (p:cm_program)) -
           ilength ((f_:cm_function_d) ::
             (rest_:(cm_function_d)list))`));
    thm exact_bounds = conv_rule(rewrite_conv(THM_LIST(size_index)),
        prefix_bounds);
    thm numeric = conj_rule(exact_bounds, size_i32);
    thm result_bounds = mp_rule(int_arith_rule(mk_imp(
        concl(numeric),
        `0i <= cm_function_prefix (p:cm_program)
            ((f_:cm_function_d) :: (rest_:(cm_function_d)list))
            ((target__pre:int) - (index__pre:int)) &&
         cm_function_prefix p (f_ :: rest_)
            (target__pre - index__pre) <= 2147483647i`)),
        numeric);
    cm_add_count_facts(cm_total_i32_from_bounds(
        `cm_function_prefix (p:cm_program)
          ((f_:cm_function_d) :: (rest_:(cm_function_d)list))
          ((target__pre:int) - (index__pre:int))`,
        result_bounds));
    thm model_i32 = from_state_bool(
        `cm_i32_code_count
          (cm_function_prefix (p:cm_program)
            ((f_:cm_function_d) :: (rest_:(cm_function_d)list))
            ((target__pre:int) - (index__pre:int)))`);
    thm sum_i32 = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(prefix_model))), model_i32);
    add_fact_st(eqt_intro_rule(sum_i32));
  }
  int result = head_count + tail_count;
  [[cst::proof]] {
    cst_set_symbolic_state(retarget_cell_st(
        cst_get_symbolic_state(), `result__addr:addr`,
        `cm_function_code_count (p:cm_program) (index__pre:int) +
          cm_function_prefix p (rest_:(cm_function_d)list)
            ((target__pre:int) - (index__pre + 1i))`,
        `cm_function_prefix p
          ((f_:cm_function_d) :: rest_)
          (target__pre - index__pre)`));
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
  return result;
}

int cmc_function_pc_total(struct cm_program *program, long long target)
    [[cst::param(`p:cm_program`, `functions_ptr:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_concrete_code_ready p <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr (cm_program_functions p)`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_concrete_code_ready p <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr (cm_program_functions p) **
       fact((__return:int) == cm_function_pc p target) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]]
{
  [[cst::proof]] {
    thm code_ready = conv_rule(rewrite_conv(THM_LIST(
        get_cm_concrete_code_ready_def())),
        from_state_bool(`cm_concrete_code_ready (p:cm_program)`));
    thm structs_ready = conjunct1_rule(code_ready);
    add_fact_st(eqt_intro_rule(structs_ready));
    add_fact_st(eqt_intro_rule(conv_rule(rewrite_conv(THM_LIST(
        get_cm_concrete_structs_ready_def())), structs_ready)));
    add_fact_st(eqt_intro_rule(conjunct2_rule(code_ready)));
    thm wf = conv_rule(rewrite_conv(THM_LIST(
        get_cm_wf_program_def(), get_cm_codegen_admissible_def())),
        from_state_bool(`cm_wf_program (p:cm_program)`));
    thm counts_ready = conv_rule(rewrite_conv(THM_LIST(
        get_cm_codegen_counts_representable_def())),
        cm_pick_conjunct(wf,
          `cm_codegen_counts_representable (p:cm_program)`));
    add_fact_st(eqt_intro_rule(conjunct1_rule(counts_ready)));

    thm program_view = apply_conversion(
        pure_rewrite_conv(THM_LIST(cm_program_context_rep_def)),
        `cm_program_context_rep (program__pre:int)
          (p:cm_program) (functions_ptr:int)`);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(eq2ent(program_view),
          TERM_LIST(`structs_ptr_total_:int`,
            `globals_ptr_total_:int`, `strings_ptr_total_:int`))));
  }
  struct cm_function *fn = program->functions;
  [[cst::proof]] {
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        cm_program_context_fold_hconv(
          `program__pre:int`, `p:cm_program`,
          `functions_ptr:int`, `structs_ptr_total_:int`,
          `globals_ptr_total_:int`, `strings_ptr_total_:int`)));
    thm functions_bound = specl_rule(TERM_LIST(
        `cm_program_functions (p:cm_program)`, `p:cm_program`, `0i`),
        cm_functions_length_le_code_size);
    thm wf_open = conv_rule(rewrite_conv(THM_LIST(
        get_cm_wf_program_def(), get_cm_codegen_admissible_def())),
        from_state_bool(`cm_wf_program (p:cm_program)`));
    thm model_upper = cm_pick_conjunct(wf_open,
        `cm_model_code_length (p:cm_program) <= 2147483647i`);
    thm model_view = apply_conversion(rewrite_conv(THM_LIST(
        get_cm_model_code_length_def())),
        `cm_model_code_length (p:cm_program)`);
    thm length_facts = cm_total_join_facts(THM_LIST(
        functions_bound, model_upper, model_view));
    add_fact_st(mp_rule(int_arith_rule(mk_imp(
        concl(length_facts),
        `0i + ilength (cm_program_functions (p:cm_program)) <=
         2147483647i`)), length_facts));
    add_fact_st(int_arith_rule(`0i <= 0i`));
    add_fact_st(int_arith_rule(
        `0i == ilength (cm_program_functions (p:cm_program)) -
          ilength (cm_program_functions p)`));
  }
  int prefix = cmc_function_prefix_total(program, fn, 0, target);
  [[cst::proof]] {
    thm prefix_model = assume_rule(
        `(retval:int) ==
         cm_function_prefix (p:cm_program)
           (cm_program_functions p) ((target__pre:int) - 0i)`);
    thm target_zero = int_arith_rule(
        `(target__pre:int) - 0i == target__pre`);
    thm normalized = conv_rule(rewrite_conv(THM_LIST(
        target_zero)), prefix_model);
    add_fact_st(normalized);
    cst_set_symbolic_state(retarget_cell_st(
        cst_get_symbolic_state(), `prefix__addr:addr`,
        `retval:int`,
        `cm_function_prefix (p:cm_program)
          (cm_program_functions p) (target__pre:int)`));

    thm prefix_bounds = specl_rule(TERM_LIST(
        `cm_program_functions (p:cm_program)`, `p:cm_program`,
        `target__pre:int`), cm_function_prefix_total_bounds);
    thm wf_open = conv_rule(rewrite_conv(THM_LIST(
        get_cm_wf_program_def(), get_cm_codegen_admissible_def())),
        from_state_bool(`cm_wf_program (p:cm_program)`));
    thm model_upper = cm_pick_conjunct(wf_open,
        `cm_model_code_length (p:cm_program) <= 2147483647i`);
    thm model_view = apply_conversion(rewrite_conv(THM_LIST(
        get_cm_model_code_length_def())),
        `cm_model_code_length (p:cm_program)`);
    thm zero_index = int_arith_rule(
        `ilength (cm_program_functions (p:cm_program)) -
          ilength (cm_program_functions p) == 0i`);
    thm exact_prefix_bounds = conv_rule(rewrite_conv(THM_LIST(
        zero_index)), prefix_bounds);
    thm numeric = cm_total_join_facts(THM_LIST(
        exact_prefix_bounds, model_upper, model_view));
    thm pc_bounds = mp_rule(int_arith_rule(mk_imp(
        concl(numeric),
        `0i <= 11i + cm_function_prefix (p:cm_program)
            (cm_program_functions p) (target__pre:int) &&
         11i + cm_function_prefix p (cm_program_functions p) target__pre <=
            2147483647i`)), numeric);
    cm_add_count_facts(cm_total_i32_from_bounds(
        `11i + cm_function_prefix (p:cm_program)
          (cm_program_functions p) (target__pre:int)`, pc_bounds));
  }
  int result = 11 + prefix;
  [[cst::proof]] {
    thm model = by_rewrite(
        `11i + cm_function_prefix (p:cm_program)
           (cm_program_functions p) (target__pre:int) ==
         cm_function_pc p target__pre`,
        THM_LIST(get_cm_function_pc_def()));
    add_fact_st(model);
    thm result_i32 = conv_rule(rewrite_conv(THM_LIST(model)),
        from_state_bool(
          `cm_i32_code_count
            (11i + cm_function_prefix (p:cm_program)
              (cm_program_functions p) (target__pre:int))`));
    add_fact_st(eqt_intro_rule(result_i32));
    cst_set_symbolic_state(retarget_cell_st(
        cst_get_symbolic_state(), `result__addr:addr`,
        `11i + cm_function_prefix (p:cm_program)
          (cm_program_functions p) (target__pre:int)`,
        `cm_function_pc (p:cm_program) (target__pre:int)`));
  }
  return result;
}
