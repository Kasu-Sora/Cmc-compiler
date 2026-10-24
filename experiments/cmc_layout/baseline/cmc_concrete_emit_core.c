#include "cmc_concrete_emit_core.h"

PROOF static void cm_open_emit_fragment(const thm code_shape) {
  thm todo_shape = beta_norm(ap_term_rule(
      `\code:(tvm_inst)list.
         code ++ (tail:(tvm_inst)list)`,
      code_shape));
  substitute_st(todo_shape);
  rewrite_st(THM_LIST(
      gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
      get_theorem_by_name("APPEND")));
}

PROOF static void cm_close_emit_fragment(const thm code_shape) {
  rewrite_st(THM_LIST(
      gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
      get_theorem_by_name("APPEND")));
  thm done_shape = beta_norm(ap_term_rule(
      `\code:(tvm_inst)list.
         (done:(tvm_inst)list) ++ code`,
      sym_rule(code_shape)));
  substitute_st(done_shape);
}

PROOF static void cm_add_opcode_fact(const term concrete,
                                     const term opcode) {
  thm code_fact = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_tvm_opcode_code_def())),
      mk_eq(concrete,
        mk_comb(`tvm_opcode_code:tvm_opcode->int`, opcode))));
  add_fact_st(code_fact);
}

PROOF static void cm_retarget_call_result(
    const term cell, const thm result) {
  struct dest_eq_results sides = dest_eq(concl(result));
  add_fact_st(result);
  cst_set_symbolic_state(retarget_cell64_st(
      cst_get_symbolic_state(), cell, sides.tm1, sides.tm2));
}

PROOF static thm cm_temp_offset_model_bridge(void) {
  thm params_wf = eqt_elim_rule(assume_rule(
      `cm_slots_wf (structs:(cm_struct_d)list)
         (cm_function_params (f:cm_function_d)) <=> true`));
  thm locals_wf = eqt_elim_rule(assume_rule(
      `cm_slots_wf (structs:(cm_struct_d)list)
         (cm_function_locals (f:cm_function_d)) <=> true`));
  thm params_size = mp_rule(specl_rule(TERM_LIST(
      `structs:(cm_struct_d)list`,
      `cm_function_params (f:cm_function_d)`),
      cm_rep_members_size_matches), params_wf);
  thm locals_size = mp_rule(specl_rule(TERM_LIST(
      `structs:(cm_struct_d)list`,
      `cm_function_locals (f:cm_function_d)`),
      cm_rep_members_size_matches), locals_wf);
  return by_rewrite(
      `8i +
         cm_rep_members_size (cm_function_params (f:cm_function_d)) +
         cm_rep_members_size (cm_function_locals f) +
         8i * (temp__pre:int) ==
       cm_temp_offset (p:cm_program) (fid:int) temp__pre`,
      THM_LIST(get_cm_temp_offset_def(), params_size, locals_size,
        assume_rule(
          `structs == cm_program_structs (p:cm_program)`),
        assume_rule(
          `(f:cm_function_d) ==
           inth (fid:int) (cm_program_functions p)`)));
}

PROOF static void cm_open_function_context(void) {
  thm context_view = apply_conversion(
      pure_rewrite_conv(THM_LIST(cm_function_context_rep_def)),
      `cm_function_context_rep (fn__pre:int)
        (f:cm_function_d) (body:int) (next:int)`);
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      rename_exists_hconv(eq2ent(context_view),
        TERM_LIST(`params_ptr_:int`, `locals_ptr_:int`))));
}

PROOF static void cm_close_function_context(void) {
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      cm_function_context_fold_hconv(
        `fn__pre:int`, `f:cm_function_d`,
        `body:int`, `next:int`,
        `params_ptr_:int`, `locals_ptr_:int`)));
}

PROOF static thm cm_finish_binary_opcode_reduction(
    const thm reduction) {
  struct dest_eq_results sides = dest_eq(concl(reduction));
  thm residual = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_tvm_opcode_code_def())),
      sides.tm2));
  return eq_mp_rule(sym_rule(reduction), residual);
}

PROOF static void cm_add_binary_opcode_case(
    const term concrete, const thm condition) {
  thm reduction = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        condition, get_cm_binary_opcode_def())),
      mk_eq(
        `tvm_opcode_code (cm_binary_opcode (op__pre:int))`,
        concrete));
  add_fact_st(sym_rule(
      cm_finish_binary_opcode_reduction(reduction)));
}

PROOF static void cm_add_binary_opcode_default(void) {
  thm reduction = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        eqf_intro_rule(assume_rule(`~(op__pre == 2i)`)),
        eqf_intro_rule(assume_rule(`~(op__pre == 3i)`)),
        eqf_intro_rule(assume_rule(`~(op__pre == 4i)`)),
        eqf_intro_rule(assume_rule(`~(op__pre == 5i)`)),
        eqf_intro_rule(assume_rule(`~(op__pre == 6i)`)),
        eqf_intro_rule(assume_rule(`~(op__pre == 7i)`)),
        eqf_intro_rule(assume_rule(`~(op__pre == 8i)`)),
        eqf_intro_rule(assume_rule(`~(op__pre == 9i)`)),
        eqf_intro_rule(assume_rule(`~(op__pre == 10i)`)),
        eqf_intro_rule(assume_rule(`~(op__pre == 11i)`)),
        get_cm_binary_opcode_def())),
      `tvm_opcode_code (cm_binary_opcode (op__pre:int)) == 12i`);
  add_fact_st(sym_rule(
      cm_finish_binary_opcode_reduction(reduction)));
}

PROOF static thm cm_model_char_from_encoded_type(void) {
  thm type_code_wf = eqt_elim_rule(assume_rule(
      `cm_type_code_wf (model_ty:cm_type) <=> true`));
  thm char_iff = mp_rule(
      spec_rule(`model_ty:cm_type`, cm_char_encode),
      type_code_wf);
  thm encoded_char = trans_rule(
      sym_rule(assume_rule(
        `(ty__pre:int) == cm_type_encode (model_ty:cm_type)`)),
      assume_rule(`(ty__pre:int) == 1i`));
  return eq_mp_rule(char_iff, encoded_char);
}

PROOF static thm cm_model_not_char_from_encoded_type(void) {
  thm type_code_wf = eqt_elim_rule(assume_rule(
      `cm_type_code_wf (model_ty:cm_type) <=> true`));
  thm char_iff = mp_rule(
      spec_rule(`model_ty:cm_type`, cm_char_encode),
      type_code_wf);
  thm not_encoded = conv_rule(
      subs_conv(THM_LIST(assume_rule(
        `(ty__pre:int) == cm_type_encode (model_ty:cm_type)`))),
      assume_rule(`~((ty__pre:int) == 1i)`));
  return eq_mp_rule(
      beta_norm(ap_term_rule(`\b:bool. ~b`, char_iff)),
      not_encoded);
}

static void cm_emit_raw(struct cm_emitter *emitter, int op,
                        long long immediate)
    [[cst::param(`ops_prefix:(int)list`, `imms_prefix:(int)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ilength ops_prefix < capacity) **
       cm_emitter_rep emitter out capacity ops_prefix imms_prefix`)]]
    [[cst::ensure(
      `cm_emitter_rep emitter out capacity
         (ops_prefix ++ [op]) (imms_prefix ++ [immediate])`)]]
{
  [[cst::proof]] {
    thm emitter_view = apply_conversion(
        pure_rewrite_conv(THM_LIST(cm_emitter_rep_def)),
        `cm_emitter_rep (emitter__pre:int) (out:int)
          (capacity:int) (ops_prefix:(int)list)
          (imms_prefix:(int)list)`);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(eq2ent(emitter_view),
          TERM_LIST(`ops_:int`, `imms_:int`))));
    add_data_at_range_st(
        `field_addr (out:int) Tcm_output Fcode_capacity`,
        `Tint`, `capacity:int`);
    cm_commit_arith_fact(
        "ilength (ops_prefix:(int)list) < (capacity:int) ==>"
        "capacity - ilength ops_prefix >= 1i");
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        specl_rule(TERM_LIST(
          `ops_:int`, `capacity:int`,
          `ilength (ops_prefix:(int)list)`),
          get_cm_open_int_fill())));
  }
  emitter->output->ops[emitter->pc] = op;
  [[cst::proof]] {
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        specl_rule(TERM_LIST(
          `ops_:int`, `ilength (ops_prefix:(int)list)`,
          `ops_prefix:(int)list`, `op__pre:int`),
          get_cm_close_int_fill())));
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        specl_rule(TERM_LIST(
          `imms_:int`, `capacity:int`,
          `ilength (ops_prefix:(int)list)`),
          get_cm_open_int64_fill())));
  }
  emitter->output->imms[emitter->pc] = immediate;
  [[cst::proof]] {
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        specl_rule(TERM_LIST(
          `imms_:int`, `ilength (ops_prefix:(int)list)`,
          `imms_prefix:(int)list`, `immediate__pre:int`),
          get_cm_close_int64_fill())));
  }
  emitter->pc = emitter->pc + 1;
  [[cst::proof]] {
    term ops_extended =
        `ops_prefix ++ [(op__pre:int)]`;
    term imms_extended =
        `imms_prefix ++ [(immediate__pre:int)]`;
    conv length_conv = then_conv(
        rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF"))),
        get_conversion_by_name("INT_REDUCE_CONV"));
    thm ops_length = apply_conversion(length_conv,
        mk_comb(`ilength:(int)list->int`, ops_extended));
    thm imms_length = apply_conversion(length_conv,
        mk_comb(`ilength:(int)list->int`, imms_extended));
    cm_commit_arith_fact(
        "ilength (ops_prefix:(int)list) < (capacity:int) ==>"
        "ilength ops_prefix + 1i <= capacity");
    cm_commit_arith_fact(
        "0i <= ilength (ops_prefix:(int)list) ==>"
        "0i <= ilength ops_prefix + 1i");
    cm_commit_arith_fact(
        "ilength (ops_prefix:(int)list) =="
        " ilength (imms_prefix:(int)list) ==>"
        "ilength ops_prefix + 1i == ilength imms_prefix + 1i");
    term subject = mk_comb(
        mk_comb(
          mk_comb(
            mk_comb(
              mk_comb(`cm_emitter_rep`, `emitter__pre:int`),
              `out:int`),
            `capacity:int`),
          ops_extended),
        imms_extended);
    thm folded = apply_conversion(
        pure_rewrite_conv(THM_LIST(
          cm_emitter_rep_def, ops_length, imms_length)),
        subject);
    term existential = dest_eq(concl(folded)).tm2;
    dest_binder_results outer = dest_sl_exists(existential);
    dest_binder_results inner = dest_sl_exists(outer.tm);
    term body = subst(TERM_PAIR_LIST(
        (term_pair){`ops_:int`, outer.v},
        (term_pair){`imms_:int`, inner.v}), inner.tm);
    term inner_existential = subst(TERM_PAIR_LIST(
        (term_pair){`ops_:int`, outer.v}), outer.tm);
    thm introduced = refl_slrule(body);
    introduced = exists_slrule(
        inner_existential, `imms_:int`, introduced);
    introduced = exists_slrule(
        existential, `ops_:int`, introduced);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        trans_slrule(introduced, eq2ent(sym_rule(folded)))));
  }
}

void cm_emit(struct cm_emitter *emitter, int op, long long immediate)
    [[cst::param(`done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `opcode:tvm_opcode`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(op == tvm_opcode_code opcode) **
       cm_emitter_plan_rep emitter out capacity done
         (TVMInst opcode immediate :: tail)`)]]
    [[cst::ensure(
      `cm_emitter_plan_rep emitter out capacity
         (done ++ [TVMInst opcode immediate]) tail`)]]
{
  [[cst::proof]] {
    thm plan_view = apply_conversion(
        pure_rewrite_conv(THM_LIST(cm_emitter_plan_rep_def)),
        `cm_emitter_plan_rep (emitter__pre:int) (out:int)
          (capacity:int) (done:(tvm_inst)list)
          (TVMInst (opcode:tvm_opcode) (immediate__pre:int) ::
             (tail:(tvm_inst)list))`);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        eq2ent(plan_view)));
    thm done_ops_length = spec_rule(
        `done:(tvm_inst)list`, cm_rep_ops_length);
    add_fact_st(done_ops_length);
    thm capacity_linear = conv_rule(
        rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
        assume_rule(
          `ilength (done:(tvm_inst)list) +
             ilength
               (TVMInst (opcode:tvm_opcode) (immediate__pre:int) ::
                  (tail:(tvm_inst)list)) <=
           (capacity:int)`));
    add_fact_st(capacity_linear);
    add_fact_st(ispec_rule(
        `tail:(tvm_inst)list`,
        get_theorem_by_name("ILENGTH_NONNEG")));
    cm_commit_arith_fact(
        "ilength (cm_rep_ops (done:(tvm_inst)list)) =="
        " ilength done ==>"
        "0i <= ilength (tail:(tvm_inst)list) ==>"
        "ilength done + 1i + ilength tail <= (capacity:int) ==>"
        "ilength (cm_rep_ops done) < capacity");
  }
  cm_emit_raw(emitter, op, immediate);
  [[cst::proof]] {
    term inst =
        `TVMInst (opcode:tvm_opcode) (immediate__pre:int)`;
    term extended =
        mk_binop(`APPEND:(tvm_inst)list->(tvm_inst)list->
                    (tvm_inst)list`,
          `done:(tvm_inst)list`,
          mk_cons(inst, `[]:(tvm_inst)list`));
    thm ops_equal = by_rewrite(
        mk_eq(
          `cm_rep_ops (done:(tvm_inst)list) ++ [(op__pre:int)]`,
          mk_comb(`cm_rep_ops:(tvm_inst)list->(int)list`, extended)),
        THM_LIST(
          assume_rule(
            `(op__pre:int) ==
             tvm_opcode_code (opcode:tvm_opcode)`),
          cm_rep_ops_append, get_cm_rep_ops_def(),
          get_tvm_inst_op_def()));
    thm imms_equal = by_rewrite(
        mk_eq(
          `cm_rep_imms (done:(tvm_inst)list) ++
             [(immediate__pre:int)]`,
          mk_comb(`cm_rep_imms:(tvm_inst)list->(int)list`, extended)),
        THM_LIST(
          cm_rep_imms_append, get_cm_rep_imms_def(),
          get_tvm_inst_imm_def()));
    substitute_st(ops_equal);
    substitute_st(imms_equal);
    conv length_conv = then_conv(
        rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF"))),
        get_conversion_by_name("INT_REDUCE_CONV"));
    thm todo_length = apply_conversion(length_conv,
        `ilength
          (TVMInst (opcode:tvm_opcode) (immediate__pre:int) ::
             (tail:(tvm_inst)list))`);
    thm extended_length = by_defs_arith(
        mk_eq(mk_comb(`ilength:(tvm_inst)list->int`, extended),
          `ilength (done:(tvm_inst)list) + 1i`),
        THM_LIST(
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF")),
        THM_LIST());
    thm capacity_pre = conv_rule(
        rewrite_conv(THM_LIST(todo_length)),
        assume_rule(
          `ilength (done:(tvm_inst)list) +
             ilength
               (TVMInst (opcode:tvm_opcode) (immediate__pre:int) ::
                  (tail:(tvm_inst)list)) <=
           (capacity:int)`));
    thm capacity_post_math = mp_rule(
        int_arith_rule(
          mk_imp(concl(capacity_pre),
            `(ilength (done:(tvm_inst)list) + 1i) +
               ilength (tail:(tvm_inst)list) <= (capacity:int)`)),
        capacity_pre);
    thm capacity_post = eq_mp_rule(
        apply_conversion(
          subs_conv(THM_LIST(sym_rule(extended_length))),
          concl(capacity_post_math)),
        capacity_post_math);
    add_fact_st(capacity_post);
    thm folded = apply_conversion(
        pure_rewrite_conv(THM_LIST(cm_emitter_plan_rep_def)),
        mk_comb(
          mk_comb(
            mk_comb(
              mk_comb(
                mk_comb(`cm_emitter_plan_rep`,
                  `emitter__pre:int`),
                `out:int`),
              `capacity:int`),
            extended),
          `tail:(tvm_inst)list`));
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        eq2ent(sym_rule(folded))));
  }
}

void cm_emit_normalize(struct cm_emitter *emitter, int ty)
    [[cst::param(`model_ty:cm_type`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true) **
       cm_emitter_plan_rep emitter out capacity done
         (cm_char_normalize_code model_ty ++ tail)`)]]
    [[cst::ensure(
      `cm_emitter_plan_rep emitter out capacity
         (done ++ cm_char_normalize_code model_ty) tail`)]]
{
  if (ty == CMC_TYPE_CHAR) {
    [[cst::proof]] {
      thm type_code_wf = eqt_elim_rule(assume_rule(
          `cm_type_code_wf (model_ty:cm_type) <=> true`));
      thm char_iff = mp_rule(
          spec_rule(`model_ty:cm_type`, cm_char_encode),
          type_code_wf);
      thm encoded_char = trans_rule(
          sym_rule(assume_rule(
            `(ty__pre:int) ==
             cm_type_encode (model_ty:cm_type)`)),
          assume_rule(`(ty__pre:int) == 1i`));
      thm model_char = eq_mp_rule(char_iff, encoded_char);
      thm code_shape = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_char_normalize_code_def(), model_char)),
          `cm_char_normalize_code (model_ty:cm_type)`);
      thm todo_shape = beta_norm(ap_term_rule(
          `\code:(tvm_inst)list.
             code ++ (tail:(tvm_inst)list)`,
          code_shape));
      substitute_st(todo_shape);
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
      thm push_code = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(get_tvm_opcode_code_def())),
          `0i == tvm_opcode_code TVMPushOp`));
      thm mod_code = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(get_tvm_opcode_code_def())),
          `12i == tvm_opcode_code TVMModOp`));
      thm add_code = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(get_tvm_opcode_code_def())),
          `8i == tvm_opcode_code TVMAddOp`));
      add_fact_st(push_code);
      add_fact_st(mod_code);
      add_fact_st(add_code);
    }
    cm_emit(emitter, CMC_OP_PUSH, 256);
    cm_emit(emitter, CMC_OP_MOD, 0);
    cm_emit(emitter, CMC_OP_PUSH, 256);
    cm_emit(emitter, CMC_OP_ADD, 0);
    cm_emit(emitter, CMC_OP_PUSH, 256);
    cm_emit(emitter, CMC_OP_MOD, 0);
    [[cst::proof]] {
      thm type_code_wf = eqt_elim_rule(assume_rule(
          `cm_type_code_wf (model_ty:cm_type) <=> true`));
      thm char_iff = mp_rule(
          spec_rule(`model_ty:cm_type`, cm_char_encode),
          type_code_wf);
      thm encoded_char = trans_rule(
          sym_rule(assume_rule(
            `(ty__pre:int) ==
             cm_type_encode (model_ty:cm_type)`)),
          assume_rule(`(ty__pre:int) == 1i`));
      thm model_char = eq_mp_rule(char_iff, encoded_char);
      thm code_shape = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_char_normalize_code_def(), model_char)),
          `cm_char_normalize_code (model_ty:cm_type)`);
      rewrite_st(THM_LIST(
          gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
          get_theorem_by_name("APPEND")));
      thm done_shape = beta_norm(ap_term_rule(
          `\code:(tvm_inst)list.
             (done:(tvm_inst)list) ++ code`,
          sym_rule(code_shape)));
      substitute_st(done_shape);
    }
  } else {
    [[cst::proof]] {
      thm type_code_wf = eqt_elim_rule(assume_rule(
          `cm_type_code_wf (model_ty:cm_type) <=> true`));
      thm char_iff = mp_rule(
          spec_rule(`model_ty:cm_type`, cm_char_encode),
          type_code_wf);
      thm not_encoded = conv_rule(
          subs_conv(THM_LIST(assume_rule(
            `(ty__pre:int) ==
             cm_type_encode (model_ty:cm_type)`))),
          assume_rule(`~((ty__pre:int) == 1i)`));
      thm not_model_char = eq_mp_rule(
          beta_norm(ap_term_rule(`\b:bool. ~b`, char_iff)),
          not_encoded);
      thm code_shape = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_char_normalize_code_def(), not_model_char)),
          `cm_char_normalize_code (model_ty:cm_type)`);
      thm todo_shape = by_rewrite(
          `cm_char_normalize_code (model_ty:cm_type) ++
             (tail:(tvm_inst)list) == tail`,
          THM_LIST(code_shape, get_theorem_by_name("APPEND")));
      substitute_st(todo_shape);
      thm done_shape = by_rewrite(
          `(done:(tvm_inst)list) ==
             done ++ cm_char_normalize_code (model_ty:cm_type)`,
          THM_LIST(code_shape, get_theorem_by_name("APPEND"),
            get_theorem_by_name("APPEND_NIL")));
      substitute_st(done_shape);
    }
  }
}

void cm_emit_load(struct cm_emitter *emitter, int ty)
    [[cst::param(`model_ty:cm_type`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true) **
       cm_emitter_plan_rep emitter out capacity done
         (cm_load_code model_ty ++ tail)`)]]
    [[cst::ensure(
      `cm_emitter_plan_rep emitter out capacity
         (done ++ cm_load_code model_ty) tail`)]]
{
  if (ty == CMC_TYPE_CHAR) {
    [[cst::proof]] {
      thm model_char = cm_model_char_from_encoded_type();
      thm code_shape = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_load_code_def(), model_char)),
          `cm_load_code (model_ty:cm_type)`);
      cm_open_emit_fragment(code_shape);
      cm_add_opcode_fact(`6i`, `TVMLoadBOp`);
    }
    cm_emit(emitter, CMC_OP_LOADB, 0);
    [[cst::proof]] {
      thm model_char = cm_model_char_from_encoded_type();
      thm code_shape = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_load_code_def(), model_char)),
          `cm_load_code (model_ty:cm_type)`);
      cm_close_emit_fragment(code_shape);
    }
  } else {
    [[cst::proof]] {
      thm not_model_char = cm_model_not_char_from_encoded_type();
      thm code_shape = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_load_code_def(), not_model_char)),
          `cm_load_code (model_ty:cm_type)`);
      cm_open_emit_fragment(code_shape);
      cm_add_opcode_fact(`4i`, `TVMLoadOp`);
    }
    cm_emit(emitter, CMC_OP_LOAD, 0);
    [[cst::proof]] {
      thm not_model_char = cm_model_not_char_from_encoded_type();
      thm code_shape = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_load_code_def(), not_model_char)),
          `cm_load_code (model_ty:cm_type)`);
      cm_close_emit_fragment(code_shape);
    }
  }
}

void cm_emit_store(struct cm_emitter *emitter, int ty)
    [[cst::param(`model_ty:cm_type`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true) **
       cm_emitter_plan_rep emitter out capacity done
         (cm_store_code model_ty ++ tail)`)]]
    [[cst::ensure(
      `cm_emitter_plan_rep emitter out capacity
         (done ++ cm_store_code model_ty) tail`)]]
{
  if (ty == CMC_TYPE_CHAR) {
    [[cst::proof]] {
      thm model_char = cm_model_char_from_encoded_type();
      thm code_shape = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_store_code_def(), model_char)),
          `cm_store_code (model_ty:cm_type)`);
      cm_open_emit_fragment(code_shape);
      cm_add_opcode_fact(`7i`, `TVMStoreBOp`);
    }
    cm_emit(emitter, CMC_OP_STOREB, 0);
    [[cst::proof]] {
      thm model_char = cm_model_char_from_encoded_type();
      thm code_shape = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_store_code_def(), model_char)),
          `cm_store_code (model_ty:cm_type)`);
      cm_close_emit_fragment(code_shape);
    }
  } else {
    [[cst::proof]] {
      thm not_model_char = cm_model_not_char_from_encoded_type();
      thm code_shape = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_store_code_def(), not_model_char)),
          `cm_store_code (model_ty:cm_type)`);
      cm_open_emit_fragment(code_shape);
      cm_add_opcode_fact(`5i`, `TVMStoreOp`);
    }
    cm_emit(emitter, CMC_OP_STORE, 0);
    [[cst::proof]] {
      thm not_model_char = cm_model_not_char_from_encoded_type();
      thm code_shape = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_store_code_def(), not_model_char)),
          `cm_store_code (model_ty:cm_type)`);
      cm_close_emit_fragment(code_shape);
    }
  }
}

void cm_emit_fp_address(struct cm_emitter *emitter, long long offset)
    [[cst::param(`done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `cm_emitter_plan_rep emitter out capacity done
         (cm_fp_relative_address_code offset ++ tail)`)]]
    [[cst::ensure(
      `cm_emitter_plan_rep emitter out capacity
         (done ++ cm_fp_relative_address_code offset) tail`)]]
{
  [[cst::proof]] {
    thm code_shape = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_fp_relative_address_code_def())),
        `cm_fp_relative_address_code (offset__pre:int)`);
    cm_open_emit_fragment(code_shape);
    cm_add_opcode_fact(`0i`, `TVMPushOp`);
    cm_add_opcode_fact(`4i`, `TVMLoadOp`);
    cm_add_opcode_fact(`8i`, `TVMAddOp`);
  }
  cm_emit(emitter, CMC_OP_PUSH, 8);
  cm_emit(emitter, CMC_OP_LOAD, 0);
  cm_emit(emitter, CMC_OP_PUSH, offset);
  cm_emit(emitter, CMC_OP_ADD, 0);
  [[cst::proof]] {
    thm code_shape = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_fp_relative_address_code_def())),
        `cm_fp_relative_address_code (offset__pre:int)`);
    cm_close_emit_fragment(code_shape);
  }
}

void cm_emit_temp_store(struct cm_function *fn, int temp,
                               struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `fid:int`,
                 `structs:(cm_struct_d)list`, `body:int`, `next:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= temp) **
       fact(structs == cm_program_structs p) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       cm_function_context_rep fn f body next **
       cm_emitter_plan_rep emitter out capacity done
         (cm_temp_store_code p fid temp ++ tail)`)]]
    [[cst::ensure(
      `fact(0i <= temp) **
       fact(structs == cm_program_structs p) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       cm_function_context_rep fn f body next **
       cm_emitter_plan_rep emitter out capacity
         (done ++ cm_temp_store_code p fid temp) tail`)]]
{
  [[cst::proof]] {
    cm_open_function_context();
    thm offset_model = cm_temp_offset_model_bridge();
    add_fact_st(offset_model);
    add_fact_st(conv_rule(rewrite_conv(
        THM_LIST(sym_rule(offset_model))),
        assume_rule(
          `cm_temp_offset (p:cm_program) (fid:int)
             (temp__pre:int) <= 2147483647i`)));
  }
  long long offset = cmc_temp_offset(fn, temp);
  [[cst::proof]] {
    thm offset_model = cm_temp_offset_model_bridge();
    thm returned = assume_rule(
        `(retval:int) ==
         8i +
           cm_rep_members_size
             (cm_function_params (f:cm_function_d)) +
           cm_rep_members_size (cm_function_locals f) +
           8i * (temp__pre:int)`);
    cm_retarget_call_result(`offset__addr:addr`,
        trans_rule(returned, offset_model));
    thm code_shape = apply_conversion(
        pure_rewrite_conv(THM_LIST(get_cm_temp_store_code_def())),
        `cm_temp_store_code (p:cm_program) (fid:int)
          (temp__pre:int)`);
    cm_open_emit_fragment(code_shape);
    cm_add_opcode_fact(`5i`, `TVMStoreOp`);
  }
  cm_emit_fp_address(emitter, offset);
  cm_emit(emitter, CMC_OP_STORE, 0);
  [[cst::proof]] {
    thm code_shape = apply_conversion(
        pure_rewrite_conv(THM_LIST(get_cm_temp_store_code_def())),
        `cm_temp_store_code (p:cm_program) (fid:int)
          (temp__pre:int)`);
    cm_close_emit_fragment(code_shape);
    cm_close_function_context();
  }
}

void cm_emit_temp_load(struct cm_function *fn, int temp,
                              struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `fid:int`,
                 `structs:(cm_struct_d)list`, `body:int`, `next:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= temp) **
       fact(structs == cm_program_structs p) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       cm_function_context_rep fn f body next **
       cm_emitter_plan_rep emitter out capacity done
         (cm_temp_load_code p fid temp ++ tail)`)]]
    [[cst::ensure(
      `fact(0i <= temp) **
       fact(structs == cm_program_structs p) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       cm_function_context_rep fn f body next **
       cm_emitter_plan_rep emitter out capacity
         (done ++ cm_temp_load_code p fid temp) tail`)]]
{
  [[cst::proof]] {
    cm_open_function_context();
    thm offset_model = cm_temp_offset_model_bridge();
    add_fact_st(offset_model);
    add_fact_st(conv_rule(rewrite_conv(
        THM_LIST(sym_rule(offset_model))),
        assume_rule(
          `cm_temp_offset (p:cm_program) (fid:int)
             (temp__pre:int) <= 2147483647i`)));
  }
  long long offset = cmc_temp_offset(fn, temp);
  [[cst::proof]] {
    thm offset_model = cm_temp_offset_model_bridge();
    thm returned = assume_rule(
        `(retval:int) ==
         8i +
           cm_rep_members_size
             (cm_function_params (f:cm_function_d)) +
           cm_rep_members_size (cm_function_locals f) +
           8i * (temp__pre:int)`);
    cm_retarget_call_result(`offset__addr:addr`,
        trans_rule(returned, offset_model));
    thm code_shape = apply_conversion(
        pure_rewrite_conv(THM_LIST(get_cm_temp_load_code_def())),
        `cm_temp_load_code (p:cm_program) (fid:int)
          (temp__pre:int)`);
    cm_open_emit_fragment(code_shape);
    cm_add_opcode_fact(`4i`, `TVMLoadOp`);
  }
  cm_emit_fp_address(emitter, offset);
  cm_emit(emitter, CMC_OP_LOAD, 0);
  [[cst::proof]] {
    thm code_shape = apply_conversion(
        pure_rewrite_conv(THM_LIST(get_cm_temp_load_code_def())),
        `cm_temp_load_code (p:cm_program) (fid:int)
          (temp__pre:int)`);
    cm_close_emit_fragment(code_shape);
    cm_close_function_context();
  }
}

int cmc_binary_opcode(int op)
    [[cst::require(`emp`)]]
    [[cst::ensure(
      `fact((__return:int) ==
         tvm_opcode_code (cm_binary_opcode op)) **
       fact(~(tvm_opcode_code (cm_binary_opcode op) == 22i))`)]]
{
  int result;
  if (op == CMC_BIN_EQ) {
    result = CMC_OP_EQ;
    [[cst::proof]] {
      cm_add_binary_opcode_case(`13i`,
          assume_rule(`op__pre == 2i`));
    }
  } else if (op == CMC_BIN_NE) {
    result = CMC_OP_NE;
    [[cst::proof]] {
      cm_add_binary_opcode_case(`14i`,
          assume_rule(`op__pre == 3i`));
    }
  } else if (op == CMC_BIN_LT) {
    result = CMC_OP_LT;
    [[cst::proof]] {
      cm_add_binary_opcode_case(`15i`,
          assume_rule(`op__pre == 4i`));
    }
  } else if (op == CMC_BIN_LE) {
    result = CMC_OP_LE;
    [[cst::proof]] {
      cm_add_binary_opcode_case(`16i`,
          assume_rule(`op__pre == 5i`));
    }
  } else if (op == CMC_BIN_GT) {
    result = CMC_OP_GT;
    [[cst::proof]] {
      cm_add_binary_opcode_case(`17i`,
          assume_rule(`op__pre == 6i`));
    }
  } else if (op == CMC_BIN_GE) {
    result = CMC_OP_GE;
    [[cst::proof]] {
      cm_add_binary_opcode_case(`18i`,
          assume_rule(`op__pre == 7i`));
    }
  } else if (op == CMC_BIN_ADD) {
    result = CMC_OP_ADD;
    [[cst::proof]] {
      cm_add_binary_opcode_case(`8i`,
          assume_rule(`op__pre == 8i`));
    }
  } else if (op == CMC_BIN_SUB) {
    result = CMC_OP_SUB;
    [[cst::proof]] {
      cm_add_binary_opcode_case(`9i`,
          assume_rule(`op__pre == 9i`));
    }
  } else if (op == CMC_BIN_MUL) {
    result = CMC_OP_MUL;
    [[cst::proof]] {
      cm_add_binary_opcode_case(`10i`,
          assume_rule(`op__pre == 10i`));
    }
  } else if (op == CMC_BIN_DIV) {
    result = CMC_OP_DIV;
    [[cst::proof]] {
      cm_add_binary_opcode_case(`11i`,
          assume_rule(`op__pre == 11i`));
    }
  } else {
    result = CMC_OP_MOD;
    [[cst::proof]] {
      cm_add_binary_opcode_default();
    }
  }
  return result;
}
