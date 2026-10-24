#include "cmc_concrete_emit_expr_leaf.h"
#include "cmc_concrete_emit_word.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_emit_plan.c"
#require "cmc_concrete_emit_word.c"


static long long cmc_const_immediate(long long value, int ty)
    [[cst::param(`model_ty:cm_type`)]]
    [[cst::require(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true)`)]]
    [[cst::ensure(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true) **
       fact(__return ==
         cm_const_immediate model_ty value__pre)`)]]
{
  if (ty == CMC_TYPE_CHAR) {
    unsigned long long bits = (unsigned long long)value;
    unsigned char byte = (unsigned char)(bits % 256ULL);
    [[cst::proof]] {
      thm type_code_wf = eqt_elim_rule(assume_rule(
          `cm_type_code_wf (model_ty:cm_type) <=> true`));
      thm char_iff = mp_rule(
          spec_rule(`model_ty:cm_type`, cm_char_encode),
          type_code_wf);
      thm encoded_char = trans_rule(
          sym_rule(assume_rule(
            `(ty__pre:int) == cm_type_encode (model_ty:cm_type)`)),
          assume_rule(`(ty__pre:int) == 1i`));
      thm model_char = eq_mp_rule(char_iff, encoded_char);
      thm concrete = spec_rule(
          `value__pre:int`, cmc_unsigned_byte0_bridge);
      thm model = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_tower_encode_byte_def())),
          `tower_encode_byte (value__pre:int) 0i`);
      add_fact_st(trans_rule(concrete, model));
      add_fact_st(model_char);
      add_fact_st(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_const_immediate_def(), model_char)),
          `cm_const_immediate
             (model_ty:cm_type) (value__pre:int)`));
    }
    return (long long)byte;
  } else {
    [[cst::proof]] {
      thm type_code_wf = eqt_elim_rule(assume_rule(
          `cm_type_code_wf (model_ty:cm_type) <=> true`));
      thm char_iff = mp_rule(
          spec_rule(`model_ty:cm_type`, cm_char_encode),
          type_code_wf);
      thm not_encoded = conv_rule(
          subs_conv(THM_LIST(assume_rule(
            `(ty__pre:int) == cm_type_encode (model_ty:cm_type)`))),
          assume_rule(`~((ty__pre:int) == 1i)`));
      thm not_model_char = eq_mp_rule(
          beta_norm(ap_term_rule(`\b:bool. ~b`, char_iff)),
          not_encoded);
      add_fact_st(not_model_char);
      add_fact_st(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_const_immediate_def(), not_model_char)),
          `cm_const_immediate
             (model_ty:cm_type) (value__pre:int)`));
    }
    return value;
  }
}


PROOF static thm cm_leaf_code_shape(const thm shape,
                                    const thm lvalue_case) {
  return by_rewrite(
      `cm_expr_code_for (p:cm_program) (fid__pre:int) (pc__pre:int)
         (temp__pre:int) (e:cm_expr) (lvalue__pre:int) ==
       (if lvalue__pre == 0i
        then cm_rcode_of
          (cm_emit_expr_pair p fid__pre pc__pre temp__pre e)
        else cm_lcode_of
          (cm_emit_expr_pair p fid__pre pc__pre temp__pre e))`,
      THM_LIST(cm_expr_code_for_def, lvalue_case,
        get_cm_emit_rvalue_def(), get_cm_emit_lvalue_def()));
}

PROOF static thm cm_push_leaf_code_shape(const thm shape,
                                     const thm lvalue_case,
                                     const term code) {
  thm selected = cm_leaf_code_shape(shape, lvalue_case);
  return trans_rule(selected, by_rewrite(
      mk_eq(rhs_of(selected), code),
      THM_LIST(shape, get_cm_emit_expr_pair_def(),
        get_cm_rcode_of_def(), get_cm_lcode_of_def(),
        get_cm_push_code_def(), lvalue_case)));
}

PROOF static thm cm_getc_code_shape(const thm shape,
                                    const thm lvalue_case,
                                    const term code) {
  thm selected = cm_leaf_code_shape(shape, lvalue_case);
  return trans_rule(selected, by_rewrite(
      mk_eq(rhs_of(selected), code),
      THM_LIST(shape, get_cm_emit_expr_pair_def(),
        get_cm_rcode_of_def(), get_cm_lcode_of_def(),
        lvalue_case)));
}

PROOF static void cm_leaf_prepare_code(const thm code_shape) {
  substitute_st(code_shape);
  rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
}

PROOF static void cm_leaf_finish_code(const thm code_shape,
                                      const int emitted) {
  if (!emitted) {
    substitute_st(sym_rule(ispec_rule(
        `done:(tvm_inst)list`,
        get_theorem_by_name("APPEND_NIL"))));
  }
  thm prefix_shape = beta_norm(ap_term_rule(
      `\code:(tvm_inst)list.
         (done:(tvm_inst)list) ++ code`,
      sym_rule(code_shape)));
  substitute_st(prefix_shape);
}

void cm_emit_const_expr(struct cm_program *program, int fid,
                        struct cm_function *fn, int pc, int temp,
                        struct cm_expr *expr, int lvalue,
                        struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `n:int`, `ty:cm_type`, `body:int`, `next:int`,
                 `functions_ptr:int`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(e == CMConstE n ty) **
       fact(cm_type_code_wf ty <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_expr_code_for p fid pc temp e lvalue ++ tail)`)]]
    [[cst::ensure(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(e == CMConstE n ty) **
       fact(cm_type_code_wf ty <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_expr_code_for p fid pc temp e lvalue) tail`)]]
{
  [[cst::proof]] {
    cm_open_expr_rep_st();
    thm value_model = by_rewrite(
        `cm_rep_expr_value (e:cm_expr) == (n:int)`,
        THM_LIST(assume_rule(
          `e == CMConstE (n:int) (ty:cm_type)`),
          get_cm_rep_expr_value_def()));
    substitute_st(value_model);
    add_fact_st(by_rewrite(
        `cm_type_encode (cm_expr_type (e:cm_expr)) ==
         cm_type_encode (ty:cm_type)`,
        THM_LIST(assume_rule(
          `e == CMConstE (n:int) (ty:cm_type)`),
          get_cm_expr_type_def())));
  }
  if (!lvalue) {
    [[cst::where(`model_ty`, `(ty:cm_type)`)]]
    long long immediate =
        cmc_const_immediate(expr->value, expr->ty);
    [[cst::proof]] {
      thm code_shape = cm_push_leaf_code_shape(
          assume_rule(`e == CMConstE (n:int) (ty:cm_type)`),
          eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
          `[TVMInst TVMPushOp
              (cm_const_immediate (ty:cm_type) (n:int))]`);
      cm_leaf_prepare_code(code_shape);
      cm_add_opcode_facts_st(`0i`, `TVMPushOp`);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`opcode`, `TVMPushOp`)]]
    cm_emit_plan(emitter, CMC_OP_PUSH, immediate);
    [[cst::proof]] {
      substitute_st(assume_rule(
          `(retval:int) ==
           cm_const_immediate (ty:cm_type) (n:int)`));
      thm code_shape = cm_push_leaf_code_shape(
          assume_rule(`e == CMConstE (n:int) (ty:cm_type)`),
          eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
          `[TVMInst TVMPushOp
              (cm_const_immediate (ty:cm_type) (n:int))]`);
      cm_leaf_finish_code(code_shape, 1);
    }
  } else {
    [[cst::proof]] {
      thm code_shape = cm_push_leaf_code_shape(
          assume_rule(`e == CMConstE (n:int) (ty:cm_type)`),
          eqf_intro_rule(assume_rule(`~(lvalue__pre == 0i)`)),
          `[]:(tvm_inst)list`);
      cm_leaf_prepare_code(code_shape);
      cm_leaf_finish_code(code_shape, 0);
    }
  }
  [[cst::proof]] {
    thm value_model = by_rewrite(
        `cm_rep_expr_value (e:cm_expr) == (n:int)`,
        THM_LIST(assume_rule(
          `e == CMConstE (n:int) (ty:cm_type)`),
          get_cm_rep_expr_value_def()));
    substitute_st(sym_rule(value_model));
    cm_close_expr_rep_st();
  }
}

PROOF static thm cm_leaf_string_address_bridge(void) {
  thm typed = eqt_elim_rule(assume_rule(
      `cm_typed_program (p:cm_program) <=> true`));
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), typed);
  thm all_wf = conjunct1_rule(conjunct2_rule(opened));
  thm concrete = mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      `cm_program_globals (p:cm_program)`,
      `cm_program_strings (p:cm_program)`, `sid:int`),
      cm_rep_string_address_matches), all_wf);
  return by_rewrite(
      `cm_rep_string_address (cm_program_globals (p:cm_program))
         (cm_program_strings p) (sid:int) ==
       cm_string_address p sid`,
      THM_LIST(concrete, get_cm_string_address_def()));
}

void cm_emit_string_expr(struct cm_program *program, int fid,
                         struct cm_function *fn, int pc, int temp,
                         struct cm_expr *expr, int lvalue,
                         struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `sid:int`, `ty:cm_type`, `body:int`, `next:int`,
                 `functions_ptr:int`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(e == CMStringE sid ty) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(0i <= sid) ** fact(sid <= 2147483647i) **
       fact(cm_typed_program p <=> true) **
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
       fact(e == CMStringE sid ty) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(0i <= sid) ** fact(sid <= 2147483647i) **
       fact(cm_typed_program p <=> true) **
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
  [[cst::proof]] {
    cm_open_expr_rep_st();
    thm value_model = by_rewrite(
        `cm_rep_expr_value (e:cm_expr) == (sid:int)`,
        THM_LIST(assume_rule(
          `e == CMStringE (sid:int) (ty:cm_type)`),
          get_cm_rep_expr_value_def()));
    substitute_st(value_model);
  }
  int string_id = (int)expr->value;
  [[cst::proof]] {
    thm cast = mp_rule(mp_rule(
        spec_rule(`sid:int`, cm_nonnegative_i32_cast),
        assume_rule(`0i <= (sid:int)`)),
        assume_rule(`(sid:int) <= 2147483647i`));
    add_fact_st(cast);
  }
  if (!lvalue) {
    [[cst::proof]] { cm_open_program_context_st(); }
    [[cst::where(`global_items`,
                  `cm_program_globals (p:cm_program)`)]]
    [[cst::where(`string_items`,
                  `cm_program_strings (p:cm_program)`)]]
    long long address = cmc_string_address(
        program->globals, program->strings, string_id);
    [[cst::proof]] {
      thm returned = assume_rule(
          `(retval:int) ==
           cm_rep_string_address
             (cm_program_globals (p:cm_program))
             (cm_program_strings p) (sid:int)`);
      cm_retarget_i64_st(`address__addr:addr`,
          trans_rule(returned, cm_leaf_string_address_bridge()));
      cm_close_program_context_st();
      thm code_shape = cm_push_leaf_code_shape(
          assume_rule(
            `e == CMStringE (sid:int) (ty:cm_type)`),
          eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
          `[TVMInst TVMPushOp (cm_string_address p sid)]`);
      cm_leaf_prepare_code(code_shape);
      cm_add_opcode_facts_st(`0i`, `TVMPushOp`);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`opcode`, `TVMPushOp`)]]
    cm_emit_plan(emitter, CMC_OP_PUSH, address);
    [[cst::proof]] {
      thm code_shape = cm_push_leaf_code_shape(
          assume_rule(
            `e == CMStringE (sid:int) (ty:cm_type)`),
          eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
          `[TVMInst TVMPushOp (cm_string_address p sid)]`);
      cm_leaf_finish_code(code_shape, 1);
    }
  } else {
    [[cst::proof]] {
      thm code_shape = cm_push_leaf_code_shape(
          assume_rule(
            `e == CMStringE (sid:int) (ty:cm_type)`),
          eqf_intro_rule(assume_rule(`~(lvalue__pre == 0i)`)),
          `[]:(tvm_inst)list`);
      cm_leaf_prepare_code(code_shape);
      cm_leaf_finish_code(code_shape, 0);
    }
  }
  [[cst::proof]] {
    thm value_model = by_rewrite(
        `cm_rep_expr_value (e:cm_expr) == (sid:int)`,
        THM_LIST(assume_rule(
          `e == CMStringE (sid:int) (ty:cm_type)`),
          get_cm_rep_expr_value_def()));
    thm sid_lower = conv_rule(rewrite_conv(THM_LIST(value_model)),
        assume_rule(
          `0i <= cm_rep_expr_value (e:cm_expr)`));
    thm sid_upper = conv_rule(rewrite_conv(THM_LIST(value_model)),
        assume_rule(
          `cm_rep_expr_value (e:cm_expr) <= 2147483647i`));
    substitute_st(sym_rule(value_model));
    add_fact_st(sid_lower);
    add_fact_st(sid_upper);
    cm_close_expr_rep_st();
  }
}

void cm_emit_getc_expr(struct cm_program *program, int fid,
                       struct cm_function *fn, int pc, int temp,
                       struct cm_expr *expr, int lvalue,
                       struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `ty:cm_type`, `body:int`, `next:int`,
                 `functions_ptr:int`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(e == CMGetcE ty) **
       fact(f == inth fid (cm_program_functions p)) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_expr_code_for p fid pc temp e lvalue ++ tail)`)]]
    [[cst::ensure(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(e == CMGetcE ty) **
       fact(f == inth fid (cm_program_functions p)) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_expr_code_for p fid pc temp e lvalue) tail`)]]
{
  [[cst::proof]] { cm_open_expr_rep_st(); }
  if (!lvalue) {
    [[cst::proof]] {
      thm code_shape = cm_getc_code_shape(
          assume_rule(`e == CMGetcE (ty:cm_type)`),
          eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
          `[TVMInst TVMGetcOp 0i]`);
      cm_leaf_prepare_code(code_shape);
      cm_add_opcode_facts_st(`24i`, `TVMGetcOp`);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`opcode`, `TVMGetcOp`)]]
    cm_emit_plan(emitter, CMC_OP_GETC, 0);
    [[cst::proof]] {
      thm code_shape = cm_getc_code_shape(
          assume_rule(`e == CMGetcE (ty:cm_type)`),
          eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
          `[TVMInst TVMGetcOp 0i]`);
      cm_leaf_finish_code(code_shape, 1);
    }
  } else {
    [[cst::proof]] {
      thm code_shape = cm_getc_code_shape(
          assume_rule(`e == CMGetcE (ty:cm_type)`),
          eqf_intro_rule(assume_rule(`~(lvalue__pre == 0i)`)),
          `[]:(tvm_inst)list`);
      cm_leaf_prepare_code(code_shape);
      cm_leaf_finish_code(code_shape, 0);
    }
  }
  [[cst::proof]] { cm_close_expr_rep_st(); }
}

PROOF static thm cm_leaf_type_size_bridge(void) {
  thm typed = eqt_elim_rule(assume_rule(
      `cm_typed_program (p:cm_program) <=> true`));
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), typed);
  return mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`, `asked:cm_type`),
      cm_rep_type_size_matches),
      eqt_elim_rule(assume_rule(
        `cm_type_code_wf (asked:cm_type) <=> true`))),
      eqt_elim_rule(assume_rule(
        `cm_type_refs (cm_program_structs (p:cm_program))
          (asked:cm_type) <=> true`))),
      conjunct1_rule(opened));
}

static long long cm_sizeof_value(struct cm_program *program,
                                 long long code)
    [[cst::param(`p:cm_program`, `asked:cm_type`,
                 `functions_ptr:int`)]]
    [[cst::require(
      `fact(code == cm_type_encode asked) **
       fact(cm_typed_program p <=> true) **
       fact(cm_type_code_wf asked <=> true) **
       fact(cm_type_refs (cm_program_structs p) asked <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr`)]]
    [[cst::ensure(
      `fact(code == cm_type_encode asked) **
       fact(cm_typed_program p <=> true) **
       fact(cm_type_code_wf asked <=> true) **
       fact(cm_type_refs (cm_program_structs p) asked <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       fact((__return:int) ==
         cm_type_size (cm_program_structs p) asked)`)]]
{
  long long result;
  [[cst::proof]] {
    thm encoded_lower = mp_rule(spec_rule(
        `asked:cm_type`, cm_type_encode_nonnegative),
        eqt_elim_rule(assume_rule(
          `cm_type_code_wf (asked:cm_type) <=> true`)));
    add_fact_st(conv_rule(rewrite_conv(THM_LIST(
        sym_rule(assume_rule(
          `(code__pre:int) == cm_type_encode (asked:cm_type)`)))),
        encoded_lower));
  }
  if (code >= 1024) {
    result = 8;
    [[cst::proof]] {
      thm ge_code = mp_rule(int_arith_rule(
          `(code__pre:int) >= 1024i ==> 1024i <= code__pre`),
          assume_rule(`(code__pre:int) >= 1024i`));
      thm ge_encoded = conv_rule(rewrite_conv(THM_LIST(
          assume_rule(
            `(code__pre:int) == cm_type_encode (asked:cm_type)`))),
          ge_code);
      thm concrete = by_rewrite(
          `cm_rep_type_size (cm_program_structs (p:cm_program))
             (cm_type_encode (asked:cm_type)) == 8i`,
          THM_LIST(get_cm_rep_type_size_def(), ge_encoded));
      thm result_model = trans_rule(
          sym_rule(concrete), cm_leaf_type_size_bridge());
      add_fact_st(result_model);
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `result__addr:addr`, `8i`,
          `cm_type_size (cm_program_structs (p:cm_program))
            (asked:cm_type)`));
    }
  } else {
    [[cst::proof]] {
      thm upper = mp_rule(int_arith_rule(
          `(code__pre:int) < 1024i ==>
           code__pre <= 2147483647i`),
          assume_rule(`(code__pre:int) < 1024i`));
      thm cast = mp_rule(mp_rule(spec_rule(
          `code__pre:int`, cm_nonnegative_i32_cast),
          assume_rule(`0i <= (code__pre:int)`)), upper);
      add_fact_st(cast);
    }
    int narrowed = (int)code;
    [[cst::proof]] { cm_open_program_context_st(); }
    [[cst::where(`structs`,
                  `cm_program_structs (p:cm_program)`)]]
    result = cmc_type_size_at(program->structs, narrowed);
    [[cst::proof]] {
      thm returned = assume_rule(
          `(retval:int) ==
           cm_rep_type_size
             (cm_program_structs (p:cm_program))
             (code__pre:int)`);
      thm encoded_return = conv_rule(rewrite_conv(THM_LIST(
          assume_rule(
            `(code__pre:int) == cm_type_encode (asked:cm_type)`))),
          returned);
      cm_retarget_i64_st(`result__addr:addr`,
          trans_rule(encoded_return, cm_leaf_type_size_bridge()));
      cm_close_program_context_st();
    }
  }
  return result;
}

long long cm_type_size_value(struct cm_program *program,
                             long long code)
    [[cst::param(`p:cm_program`, `asked:cm_type`,
                 `functions_ptr:int`)]]
    [[cst::require(
      `fact(code == cm_type_encode asked) **
       fact(cm_typed_program p <=> true) **
       fact(cm_type_code_wf asked <=> true) **
       fact(cm_type_refs (cm_program_structs p) asked <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr`)]]
    [[cst::ensure(
      `fact(code == cm_type_encode asked) **
       fact(cm_typed_program p <=> true) **
       fact(cm_type_code_wf asked <=> true) **
       fact(cm_type_refs (cm_program_structs p) asked <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       fact((__return:int) ==
         cm_type_size (cm_program_structs p) asked)`)]]
{
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`asked`, `(asked:cm_type)`)]]
  [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
  return cm_sizeof_value(program, code);
}

void cm_emit_sizeof_expr(struct cm_program *program, int fid,
                         struct cm_function *fn, int pc, int temp,
                         struct cm_expr *expr, int lvalue,
                         struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `asked:cm_type`, `ty:cm_type`, `body:int`, `next:int`,
                 `functions_ptr:int`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(e == CMSizeofE asked ty) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_typed_program p <=> true) **
       fact(cm_type_code_wf asked <=> true) **
       fact(cm_type_refs (cm_program_structs p) asked <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_expr_code_for p fid pc temp e lvalue ++ tail)`)]]
    [[cst::ensure(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(e == CMSizeofE asked ty) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_typed_program p <=> true) **
       fact(cm_type_code_wf asked <=> true) **
       fact(cm_type_refs (cm_program_structs p) asked <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_expr_code_for p fid pc temp e lvalue) tail`)]]
{
  [[cst::proof]] {
    cm_open_expr_rep_st();
    thm value_model = by_rewrite(
        `cm_rep_expr_value (e:cm_expr) ==
         cm_type_encode (asked:cm_type)`,
        THM_LIST(assume_rule(
          `e == CMSizeofE (asked:cm_type) (ty:cm_type)`),
          get_cm_rep_expr_value_def()));
    substitute_st(value_model);
  }
  if (!lvalue) {
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`asked`, `(asked:cm_type)`)]]
    [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
    long long size = cm_sizeof_value(program, expr->value);
    [[cst::proof]] {
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `size__addr:addr`, `retval:int`,
          `cm_type_size (cm_program_structs (p:cm_program))
            (asked:cm_type)`));
    }
    [[cst::proof]] {
      thm code_shape = cm_push_leaf_code_shape(
          assume_rule(
            `e == CMSizeofE (asked:cm_type) (ty:cm_type)`),
          eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
          `[TVMInst TVMPushOp
              (cm_type_size (cm_program_structs p) asked)]`);
      cm_leaf_prepare_code(code_shape);
      cm_add_opcode_facts_st(`0i`, `TVMPushOp`);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`opcode`, `TVMPushOp`)]]
    cm_emit_plan(emitter, CMC_OP_PUSH, size);
    [[cst::proof]] {
      thm code_shape = cm_push_leaf_code_shape(
          assume_rule(
            `e == CMSizeofE (asked:cm_type) (ty:cm_type)`),
          eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
          `[TVMInst TVMPushOp
              (cm_type_size (cm_program_structs p) asked)]`);
      cm_leaf_finish_code(code_shape, 1);
    }
  } else {
    [[cst::proof]] {
      thm code_shape = cm_push_leaf_code_shape(
          assume_rule(
            `e == CMSizeofE (asked:cm_type) (ty:cm_type)`),
          eqf_intro_rule(assume_rule(`~(lvalue__pre == 0i)`)),
          `[]:(tvm_inst)list`);
      cm_leaf_prepare_code(code_shape);
      cm_leaf_finish_code(code_shape, 0);
    }
  }
  [[cst::proof]] {
    thm value_model = by_rewrite(
        `cm_rep_expr_value (e:cm_expr) ==
         cm_type_encode (asked:cm_type)`,
        THM_LIST(assume_rule(
          `e == CMSizeofE (asked:cm_type) (ty:cm_type)`),
          get_cm_rep_expr_value_def()));
    substitute_st(sym_rule(value_model));
    cm_close_expr_rep_st();
  }
}

PROOF static void cm_add_member_value_facts_st(void) {
  cm_add_count_facts(from_state_bool(
      `cm_i32_code_count (base_ty__pre:int)`));
  thm code_eq = assume_rule(
      `(base_ty__pre:int) == cm_type_encode (base:cm_type)`);
  thm type_wf = from_state_bool(
      `cm_type_code_wf (base:cm_type)`);
  thm valid = conv_rule(rewrite_conv(THM_LIST(
      get_cm_member_valid_def())), from_state_bool(
        `cm_member_valid (p:cm_program) (base:cm_type)
          (mid__pre:int)`));
  thm pointer = conjunct1_rule(valid);
  thm rest = conjunct2_rule(valid);
  thm structure = conjunct1_rule(rest);
  rest = conjunct2_rule(rest);
  thm sid_nonnegative = conjunct1_rule(rest);
  rest = conjunct2_rule(rest);
  thm sid_upper = conjunct1_rule(rest);
  rest = conjunct2_rule(rest);
  thm mid_nonnegative = conjunct1_rule(rest);
  thm sid_eq = match_mp_rule(match_mp_rule(match_mp_rule(
      spec_rule(`base:cm_type`, cm_encoded_member_sid),
      type_wf), pointer), structure);
  thm threshold = mp_rule(spec_rule(
      `base:cm_type`, cm_pointer_encode_threshold), type_wf);
  thm encoded_threshold = eq_mp_rule(sym_rule(threshold), pointer);
  add_fact_st(conv_rule(rewrite_conv(THM_LIST(
      sym_rule(code_eq))), encoded_threshold));
  add_fact_st(conv_rule(rewrite_conv(THM_LIST(
      sym_rule(code_eq), sym_rule(sid_eq))), sid_nonnegative));
  add_fact_st(sid_nonnegative);
  add_fact_st(mid_nonnegative);
  thm typed = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), from_state_bool(
        `cm_typed_program (p:cm_program)`));
  thm structs_wf = conjunct1_rule(typed);
  thm selected = mp_rule(mp_rule(spec_rule(
      `cm_struct_id (cm_pointee (base:cm_type))`, structs_wf),
      sid_nonnegative), sid_upper);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_struct_wf_def())), selected);
  thm slots_wf = conjunct1_rule(conjunct2_rule(opened));
  add_fact_st(eqt_intro_rule(slots_wf));
}

int cm_member_array_value_context(struct cm_program *program,
                                  int base_ty, int mid)
    [[cst::param(`p:cm_program`, `base:cm_type`,
                 `functions_ptr:int`)]]
    [[cst::require(
      `fact(base_ty == cm_type_encode base) **
       fact(cm_i32_code_count base_ty <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(cm_type_code_wf base <=> true) **
       fact(cm_member_valid p base mid <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr`)]]
    [[cst::ensure(
      `fact(base_ty == cm_type_encode base) **
       fact(cm_i32_code_count base_ty <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(cm_type_code_wf base <=> true) **
       fact(cm_member_valid p base mid <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       fact((__return:int) == cm_member_array_code p base mid)`)]]
{
  [[cst::proof]] {
    cm_add_member_value_facts_st();
    cm_open_program_context_st();
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`base`, `(base:cm_type)`)]]
  [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
  int result = cmc_member_array(program, base_ty, mid);
  [[cst::proof]] {
    cm_close_program_context_st();
  }
  return result;
}

long long cm_member_offset_value_context(struct cm_program *program,
                                         int base_ty, int mid)
    [[cst::param(`p:cm_program`, `base:cm_type`,
                 `functions_ptr:int`)]]
    [[cst::require(
      `fact(base_ty == cm_type_encode base) **
       fact(cm_i32_code_count base_ty <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(cm_type_code_wf base <=> true) **
       fact(cm_member_valid p base mid <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr`)]]
    [[cst::ensure(
      `fact(base_ty == cm_type_encode base) **
       fact(cm_i32_code_count base_ty <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(cm_type_code_wf base <=> true) **
       fact(cm_member_valid p base mid <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       fact((__return:int) ==
         cm_member_offset (cm_program_structs p)
           (cm_struct_id (cm_pointee base)) mid)`)]]
{
  [[cst::proof]] {
    cm_add_member_value_facts_st();
  }
  int pointee = cmc_pointee(base_ty);
  [[cst::proof]] {
    thm rem_nonnegative = mp_rule(specl_rule(TERM_LIST(
        `retval:int`, `1024i`),
        get_theorem_by_name("INT_REM_POS")),
        int_arith_rule(`~(1024i == 0i)`));
    thm rem_upper = mp_rule(specl_rule(TERM_LIST(
        `retval:int`, `1024i`),
        get_theorem_by_name("INT_LT_REM")),
        int_arith_rule(`0i < 1024i`));
    add_fact_st(mp_rule(mp_rule(int_arith_rule(
        `0i <= (retval:int) rem 1024i ==>
         retval rem 1024i < 1024i ==>
         --2147483648i <= retval rem 1024i - 2i`),
        rem_nonnegative), rem_upper));
    add_fact_st(mp_rule(mp_rule(int_arith_rule(
        `0i <= (retval:int) rem 1024i ==>
         retval rem 1024i < 1024i ==>
         retval rem 1024i - 2i <= 2147483647i`),
        rem_nonnegative), rem_upper));
  }
  int sid = (pointee % 1024) - 2;
  [[cst::proof]] {
    thm code_eq = assume_rule(
        `(base_ty__pre:int) == cm_type_encode (base:cm_type)`);
    thm type_wf = from_state_bool(
        `cm_type_code_wf (base:cm_type)`);
    thm valid = conv_rule(rewrite_conv(THM_LIST(
        get_cm_member_valid_def())), from_state_bool(
          `cm_member_valid (p:cm_program) (base:cm_type)
            (mid__pre:int)`));
    thm pointer = conjunct1_rule(valid);
    thm structure = conjunct1_rule(conjunct2_rule(valid));
    thm sid_eq = match_mp_rule(match_mp_rule(match_mp_rule(
        spec_rule(`base:cm_type`, cm_encoded_member_sid),
        type_wf), pointer), structure);
    thm pointee_eq = assume_rule(
        `(retval:int) == (base_ty__pre:int) - 1024i`);
    thm pointee_model = conv_rule(rewrite_conv(THM_LIST(
        code_eq)), pointee_eq);
    thm concrete_sid = by_rewrite(
        `((cm_type_encode (base:cm_type) - 1024i) rem 1024i) -
           2i ==
         cm_struct_id (cm_pointee base)`,
        THM_LIST(sid_eq));
    substitute_st(trans_rule(
        beta_norm(ap_term_rule(`\z:int. z rem 1024i - 2i`,
          pointee_model)), concrete_sid));
    cm_open_program_context_st();
  }
  [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
  long long result = cmc_member_offset_at(program->structs, sid, mid);
  [[cst::proof]] {
    thm valid = conv_rule(rewrite_conv(THM_LIST(
        get_cm_member_valid_def())), from_state_bool(
          `cm_member_valid (p:cm_program) (base:cm_type)
            (mid__pre:int)`));
    thm rest = conjunct2_rule(conjunct2_rule(valid));
    thm sid_nonnegative = conjunct1_rule(rest);
    rest = conjunct2_rule(rest);
    thm sid_upper = conjunct1_rule(rest);
    thm slots_wf = from_state_bool(
        `cm_slots_wf (cm_program_structs (p:cm_program))
          (cm_struct_members
            (inth (cm_struct_id (cm_pointee (base:cm_type)))
              (cm_program_structs p)))`);
    thm bridge = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`,
        `cm_struct_id (cm_pointee (base:cm_type))`,
        `mid__pre:int`), cm_rep_struct_member_prefix_matches),
        sid_nonnegative), sid_upper), slots_wf);
    thm returned = assume_rule(
        `(retval_1:int) ==
         cm_rep_struct_member_prefix
           (cm_program_structs (p:cm_program))
           (cm_struct_id (cm_pointee (base:cm_type)))
           (mid__pre:int)`);
    cm_retarget_i64_st(`result__addr:addr`,
        trans_rule(returned, bridge));
    cm_close_program_context_st();
  }
  return result;
}
