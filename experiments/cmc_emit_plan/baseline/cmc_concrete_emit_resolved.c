#include "cmc_concrete_emit_resolved.h"

PROOF static void cm_resolved_add_opcode_fact(const term concrete,
                                               const term opcode) {
  thm code_fact = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_tvm_opcode_code_def())),
      mk_eq(concrete,
        mk_comb(`tvm_opcode_code:tvm_opcode->int`, opcode))));
  add_fact_st(code_fact);
}

PROOF static thm cm_resolved_emitter_fold_hconv(
    const term program, const term emitter, const term out,
    const term capacity, const term resolved_prefix,
    const term raw_prefix) {
  term subject = mk_comb(
      mk_comb(
        mk_comb(
          mk_comb(
            mk_comb(`cm_resolved_emitter_rep`, program), emitter),
          out),
        capacity),
      resolved_prefix);
  thm view = apply_conversion(
      pure_rewrite_conv(THM_LIST(cm_resolved_emitter_rep_def)), subject);
  term existential = dest_eq(concl(view)).tm2;
  dest_binder_results outer = dest_sl_exists(existential);
  term body = subst(TERM_PAIR_LIST(
      (term_pair){raw_prefix, outer.v}), outer.tm);
  thm introduced = refl_slrule(body);
  introduced = exists_slrule(existential, raw_prefix, introduced);
  return trans_slrule(introduced, eq2ent(sym_rule(view)));
}

PROOF static void cm_open_resolved_emitter(void) {
  thm view = apply_conversion(
      pure_rewrite_conv(THM_LIST(cm_resolved_emitter_rep_def)),
      `cm_resolved_emitter_rep (p:cm_program) (emitter__pre:int)
        (out:int) (capacity:int) (done:(tvm_inst)list)`);
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      rename_exists_hconv(eq2ent(view),
        TERM_LIST(`raw_prefix_:((tvm_inst)list)`))));
}

PROOF static void cm_prepare_resolved_fragment(
    const term raw_fragment, const term resolved_fragment,
    const thm fragment_patch, const thm resolved_capacity_fact) {
  thm prefix_patch = assume_rule(
      `cm_patch_code (p:cm_program) (raw_prefix_:(tvm_inst)list) ==
       (done:(tvm_inst)list)`);
  thm prefix_patch_length = specl_rule(TERM_LIST(
      `p:cm_program`, `raw_prefix_:(tvm_inst)list`),
      cm_patch_code_length);
  thm prefix_length = trans_rule(sym_rule(prefix_patch_length),
      ap_term_rule(`ilength:(tvm_inst)list->int`, prefix_patch));
  add_fact_st(prefix_length);

  thm fragment_patch_length = specl_rule(TERM_LIST(
      `p:cm_program`, raw_fragment), cm_patch_code_length);
  thm fragment_length = trans_rule(sym_rule(fragment_patch_length),
      ap_term_rule(`ilength:(tvm_inst)list->int`, fragment_patch));
  add_fact_st(fragment_length);
  thm sum_length = mk_binop_rule(`(+):int->int->int`,
      prefix_length, fragment_length);
  thm capacity_shape = mk_binop_rule(`(<=):int->int->bool`,
      sum_length, refl_rule(`capacity:int`));
  thm raw_capacity = eq_mp_rule(sym_rule(capacity_shape),
                                resolved_capacity_fact);
  add_fact_st(raw_capacity);

  term plan = mk_comb(
      mk_comb(
        mk_comb(
          mk_comb(
            mk_comb(`cm_emitter_plan_rep`, `emitter__pre:int`),
            `out:int`),
          `capacity:int`),
        `raw_prefix_:(tvm_inst)list`),
      raw_fragment);
  thm plan_view = apply_conversion(
      pure_rewrite_conv(THM_LIST(cm_emitter_plan_rep_def)), plan);
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      eq2ent(sym_rule(plan_view))));
}

PROOF static void cm_expose_core_fragment(const term raw_fragment) {
  thm append_nil = ispec_rule(
      raw_fragment, get_theorem_by_name("APPEND_NIL"));
  thm plan_shape = beta_norm(ap_term_rule(
      `\todo:(tvm_inst)list.
         cm_emitter_plan_rep (emitter__pre:int) (out:int)
           (capacity:int) (raw_prefix_:(tvm_inst)list) todo`,
      sym_rule(append_nil)));
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      eq2ent(plan_shape)));
}

PROOF static void cm_finish_resolved_fragment(
    const term raw_fragment, const term resolved_fragment,
    const thm fragment_patch) {
  term raw_extended = mk_binop(
      `APPEND:(tvm_inst)list->(tvm_inst)list->(tvm_inst)list`,
      `raw_prefix_:(tvm_inst)list`, raw_fragment);
  term resolved_extended = mk_binop(
      `APPEND:(tvm_inst)list->(tvm_inst)list->(tvm_inst)list`,
      `done:(tvm_inst)list`, resolved_fragment);
  term plan = mk_comb(
      mk_comb(
        mk_comb(
          mk_comb(
            mk_comb(`cm_emitter_plan_rep`, `emitter__pre:int`),
            `out:int`),
          `capacity:int`),
        raw_extended),
      `[]:(tvm_inst)list`);
  thm plan_view = apply_conversion(
      pure_rewrite_conv(THM_LIST(
        cm_emitter_plan_rep_def, get_theorem_by_name("ILENGTH_DEF"))),
      plan);
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      eq2ent(plan_view)));

  thm extended_patch = by_rewrite(
      mk_eq(mk_comb(mk_comb(`cm_patch_code`, `p:cm_program`),
                     raw_extended),
            resolved_extended),
      THM_LIST(cm_patch_code_append, fragment_patch,
        assume_rule(
          `cm_patch_code (p:cm_program)
             (raw_prefix_:(tvm_inst)list) ==
           (done:(tvm_inst)list)`)));
  add_fact_st(extended_patch);
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      cm_resolved_emitter_fold_hconv(
        `p:cm_program`, `emitter__pre:int`, `out:int`, `capacity:int`,
        resolved_extended, raw_extended)));
}

PROOF static thm cm_prove_patch_char_normalize(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (ty:cm_type).
         cm_patch_code p (cm_char_normalize_code ty) ==
         cm_char_normalize_code ty`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(ty:cm_type) == CMCharTy`, "Hchar");
  CONV_TAC(cases[0], then_conv(
      rewrite_conv(THM_LIST(
        get_cm_char_normalize_code_def(),
        eqt_intro_rule(assume_rule(`(ty:cm_type) == CMCharTy`)),
        cm_patch_code_def, cm_patch_inst_def,
        get_tvm_opcode_code_def())),
      get_conversion_by_name("INT_REDUCE_CONV")));
  CONV_TAC(cases[1], then_conv(
      rewrite_conv(THM_LIST(
        get_cm_char_normalize_code_def(),
        eqf_intro_rule(assume_rule(`~((ty:cm_type) == CMCharTy)`)),
        cm_patch_code_def, cm_patch_inst_def,
        get_tvm_opcode_code_def())),
      get_conversion_by_name("INT_REDUCE_CONV")));
  return gnode_prove(root);
}
PROOF static thm cm_patch_char_normalize =
    cm_prove_patch_char_normalize();

PROOF static thm cm_prove_patch_load(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (ty:cm_type).
         cm_patch_code p (cm_load_code ty) == cm_load_code ty`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(ty:cm_type) == CMCharTy`, "Hchar");
  CONV_TAC(cases[0], then_conv(
      rewrite_conv(THM_LIST(
        get_cm_load_code_def(),
        eqt_intro_rule(assume_rule(`(ty:cm_type) == CMCharTy`)),
        cm_patch_code_def, cm_patch_inst_def,
        get_tvm_opcode_code_def())),
      get_conversion_by_name("INT_REDUCE_CONV")));
  CONV_TAC(cases[1], then_conv(
      rewrite_conv(THM_LIST(
        get_cm_load_code_def(),
        eqf_intro_rule(assume_rule(`~((ty:cm_type) == CMCharTy)`)),
        cm_patch_code_def, cm_patch_inst_def,
        get_tvm_opcode_code_def())),
      get_conversion_by_name("INT_REDUCE_CONV")));
  return gnode_prove(root);
}
PROOF static thm cm_patch_load = cm_prove_patch_load();

PROOF static thm cm_prove_patch_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (ty:cm_type).
         cm_patch_code p (cm_store_code ty) == cm_store_code ty`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(ty:cm_type) == CMCharTy`, "Hchar");
  CONV_TAC(cases[0], then_conv(
      rewrite_conv(THM_LIST(
        get_cm_store_code_def(),
        eqt_intro_rule(assume_rule(`(ty:cm_type) == CMCharTy`)),
        cm_patch_code_def, cm_patch_inst_def,
        get_tvm_opcode_code_def())),
      get_conversion_by_name("INT_REDUCE_CONV")));
  CONV_TAC(cases[1], then_conv(
      rewrite_conv(THM_LIST(
        get_cm_store_code_def(),
        eqf_intro_rule(assume_rule(`~((ty:cm_type) == CMCharTy)`)),
        cm_patch_code_def, cm_patch_inst_def,
        get_tvm_opcode_code_def())),
      get_conversion_by_name("INT_REDUCE_CONV")));
  return gnode_prove(root);
}
PROOF static thm cm_patch_store = cm_prove_patch_store();

PROOF static thm cm_prove_patch_fp_address(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (offset:int).
         cm_patch_code p (cm_fp_relative_address_code offset) ==
         cm_fp_relative_address_code offset`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, then_conv(
      rewrite_conv(THM_LIST(
        get_cm_fp_relative_address_code_def(),
        cm_patch_code_def, cm_patch_inst_def,
        get_tvm_opcode_code_def())),
      get_conversion_by_name("INT_REDUCE_CONV")));
  return gnode_prove(root);
}
PROOF static thm cm_patch_fp_address = cm_prove_patch_fp_address();

PROOF static thm cm_prove_patch_temp_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (temp:int).
         cm_patch_code p (cm_temp_store_code p fid temp) ==
         cm_temp_store_code p fid temp`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, then_conv(
      rewrite_conv(THM_LIST(
        get_cm_temp_store_code_def(), cm_patch_code_append,
        cm_patch_fp_address, cm_patch_code_def, cm_patch_inst_def,
        get_tvm_opcode_code_def())),
      get_conversion_by_name("INT_REDUCE_CONV")));
  return gnode_prove(root);
}
PROOF static thm cm_patch_temp_store = cm_prove_patch_temp_store();

PROOF static thm cm_prove_patch_temp_load(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (temp:int).
         cm_patch_code p (cm_temp_load_code p fid temp) ==
         cm_temp_load_code p fid temp`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, then_conv(
      rewrite_conv(THM_LIST(
        get_cm_temp_load_code_def(), cm_patch_code_append,
        cm_patch_fp_address, cm_patch_code_def, cm_patch_inst_def,
        get_tvm_opcode_code_def())),
      get_conversion_by_name("INT_REDUCE_CONV")));
  return gnode_prove(root);
}
PROOF static thm cm_patch_temp_load = cm_prove_patch_temp_load();

void cm_emit_resolved(struct cm_emitter *emitter, int op,
                      long long immediate)
    [[cst::param(`p:cm_program`, `done:(tvm_inst)list`,
                 `opcode:tvm_opcode`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(op == tvm_opcode_code opcode) **
       fact(~(tvm_opcode_code opcode == 22i)) **
       fact(ilength done + 1i <= capacity) **
       cm_resolved_emitter_rep p emitter out capacity done`)]]
    [[cst::ensure(
      `cm_resolved_emitter_rep p emitter out capacity
         (done ++ [TVMInst opcode immediate])`)]]
{
  [[cst::proof]] {
    term raw_fragment =
        `[TVMInst (opcode:tvm_opcode) (immediate__pre:int)]`;
    thm fragment_patch = by_rewrite(
        `cm_patch_code (p:cm_program)
           [TVMInst (opcode:tvm_opcode) (immediate__pre:int)] ==
         [TVMInst opcode immediate__pre]`,
        THM_LIST(cm_patch_code_def, cm_patch_inst_def,
          assume_rule(
            `~(tvm_opcode_code (opcode:tvm_opcode) == 22i)`)));
    cm_open_resolved_emitter();
    thm singleton_length = by_defs_arith(
        `ilength [TVMInst (opcode:tvm_opcode) (immediate__pre:int)] == 1i`,
        THM_LIST(get_theorem_by_name("ILENGTH_DEF")), THM_LIST());
    thm sum_shape = mk_binop_rule(`(+):int->int->int`,
        refl_rule(`ilength (done:(tvm_inst)list)`), singleton_length);
    thm capacity_shape = mk_binop_rule(`(<=):int->int->bool`,
        sum_shape, refl_rule(`capacity:int`));
    thm capacity_fact = eq_mp_rule(sym_rule(capacity_shape),
        assume_rule(
          `ilength (done:(tvm_inst)list) + 1i <= (capacity:int)`));
    cm_prepare_resolved_fragment(raw_fragment, raw_fragment,
                                 fragment_patch, capacity_fact);
  }
  cm_emit(emitter, op, immediate);
  [[cst::proof]] {
    term fragment =
        `[TVMInst (opcode:tvm_opcode) (immediate__pre:int)]`;
    thm fragment_patch = by_rewrite(
        `cm_patch_code (p:cm_program)
           [TVMInst (opcode:tvm_opcode) (immediate__pre:int)] ==
         [TVMInst opcode immediate__pre]`,
        THM_LIST(cm_patch_code_def, cm_patch_inst_def,
          assume_rule(
            `~(tvm_opcode_code (opcode:tvm_opcode) == 22i)`)));
    cm_finish_resolved_fragment(fragment, fragment, fragment_patch);
  }
}

void cm_emit_resolved_call(struct cm_emitter *emitter, int function_id)
    [[cst::param(`p:cm_program`, `done:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ilength done + 1i <= capacity) **
       cm_resolved_emitter_rep p emitter out capacity done`)]]
    [[cst::ensure(
      `cm_resolved_emitter_rep p emitter out capacity
         (done ++ [TVMInst TVMCallOp
                    (cm_function_pc p function_id)])`)]]
{
  [[cst::proof]] {
    term raw_fragment =
        `[TVMInst TVMCallOp (function_id__pre:int)]`;
    term resolved_fragment =
        `[TVMInst TVMCallOp
           (cm_function_pc (p:cm_program) (function_id__pre:int))]`;
    thm fragment_patch = eqt_elim_rule(apply_conversion(
        then_conv(
          rewrite_conv(THM_LIST(
            cm_patch_code_def, cm_patch_inst_def,
            get_tvm_opcode_code_def())),
          get_conversion_by_name("INT_REDUCE_CONV")),
        mk_eq(mk_comb(mk_comb(`cm_patch_code`, `p:cm_program`),
                       raw_fragment), resolved_fragment)));
    thm singleton_length = by_defs_arith(
        mk_eq(
          mk_comb(`ilength:(tvm_inst)list->int`, resolved_fragment),
          `1i:int`),
        THM_LIST(get_theorem_by_name("ILENGTH_DEF")), THM_LIST());
    thm sum_shape = mk_binop_rule(`(+):int->int->int`,
        refl_rule(`ilength (done:(tvm_inst)list)`), singleton_length);
    thm capacity_shape = mk_binop_rule(`(<=):int->int->bool`,
        sum_shape, refl_rule(`capacity:int`));
    thm capacity_fact = eq_mp_rule(sym_rule(capacity_shape),
        assume_rule(
          `ilength (done:(tvm_inst)list) + 1i <= (capacity:int)`));
    cm_open_resolved_emitter();
    cm_prepare_resolved_fragment(raw_fragment, resolved_fragment,
                                 fragment_patch, capacity_fact);
    cm_resolved_add_opcode_fact(`22i`, `TVMCallOp`);
  }
  cm_emit(emitter, CMC_OP_CALL, function_id);
  [[cst::proof]] {
    term raw_fragment =
        `[TVMInst TVMCallOp (function_id__pre:int)]`;
    term resolved_fragment =
        `[TVMInst TVMCallOp
           (cm_function_pc (p:cm_program) (function_id__pre:int))]`;
    thm fragment_patch = eqt_elim_rule(apply_conversion(
        then_conv(
          rewrite_conv(THM_LIST(
            cm_patch_code_def, cm_patch_inst_def,
            get_tvm_opcode_code_def())),
          get_conversion_by_name("INT_REDUCE_CONV")),
        mk_eq(mk_comb(mk_comb(`cm_patch_code`, `p:cm_program`),
                       raw_fragment), resolved_fragment)));
    cm_finish_resolved_fragment(raw_fragment, resolved_fragment,
                                fragment_patch);
  }
}

void cm_emit_resolved_normalize(struct cm_emitter *emitter, int ty)
    [[cst::param(`p:cm_program`, `model_ty:cm_type`,
                 `done:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true) **
       fact(ilength done + ilength (cm_char_normalize_code model_ty) <=
              capacity) **
       cm_resolved_emitter_rep p emitter out capacity done`)]]
    [[cst::ensure(
      `cm_resolved_emitter_rep p emitter out capacity
         (done ++ cm_char_normalize_code model_ty)`)]]
{
  [[cst::proof]] {
    term fragment =
        `cm_char_normalize_code (model_ty:cm_type)`;
    thm fragment_patch = specl_rule(TERM_LIST(
        `p:cm_program`, `model_ty:cm_type`),
        cm_patch_char_normalize);
    thm capacity_fact = assume_rule(
        `ilength (done:(tvm_inst)list) +
           ilength (cm_char_normalize_code (model_ty:cm_type)) <=
         (capacity:int)`);
    cm_open_resolved_emitter();
    cm_prepare_resolved_fragment(fragment, fragment,
                                 fragment_patch, capacity_fact);
    cm_expose_core_fragment(fragment);
  }
  [[cst::where(`tail`, `[]:(tvm_inst)list`)]]
  cm_emit_normalize(emitter, ty);
  [[cst::proof]] {
    term fragment =
        `cm_char_normalize_code (model_ty:cm_type)`;
    thm fragment_patch = specl_rule(TERM_LIST(
        `p:cm_program`, `model_ty:cm_type`),
        cm_patch_char_normalize);
    cm_finish_resolved_fragment(fragment, fragment, fragment_patch);
  }
}

void cm_emit_resolved_load(struct cm_emitter *emitter, int ty)
    [[cst::param(`p:cm_program`, `model_ty:cm_type`,
                 `done:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true) **
       fact(ilength done + ilength (cm_load_code model_ty) <= capacity) **
       cm_resolved_emitter_rep p emitter out capacity done`)]]
    [[cst::ensure(
      `cm_resolved_emitter_rep p emitter out capacity
         (done ++ cm_load_code model_ty)`)]]
{
  [[cst::proof]] {
    term fragment = `cm_load_code (model_ty:cm_type)`;
    thm fragment_patch = specl_rule(TERM_LIST(
        `p:cm_program`, `model_ty:cm_type`), cm_patch_load);
    thm capacity_fact = assume_rule(
        `ilength (done:(tvm_inst)list) +
           ilength (cm_load_code (model_ty:cm_type)) <= (capacity:int)`);
    cm_open_resolved_emitter();
    cm_prepare_resolved_fragment(fragment, fragment,
                                 fragment_patch, capacity_fact);
    cm_expose_core_fragment(fragment);
  }
  [[cst::where(`tail`, `[]:(tvm_inst)list`)]]
  cm_emit_load(emitter, ty);
  [[cst::proof]] {
    term fragment = `cm_load_code (model_ty:cm_type)`;
    thm fragment_patch = specl_rule(TERM_LIST(
        `p:cm_program`, `model_ty:cm_type`), cm_patch_load);
    cm_finish_resolved_fragment(fragment, fragment, fragment_patch);
  }
}

void cm_emit_resolved_store(struct cm_emitter *emitter, int ty)
    [[cst::param(`p:cm_program`, `model_ty:cm_type`,
                 `done:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true) **
       fact(ilength done + ilength (cm_store_code model_ty) <= capacity) **
       cm_resolved_emitter_rep p emitter out capacity done`)]]
    [[cst::ensure(
      `cm_resolved_emitter_rep p emitter out capacity
         (done ++ cm_store_code model_ty)`)]]
{
  [[cst::proof]] {
    term fragment = `cm_store_code (model_ty:cm_type)`;
    thm fragment_patch = specl_rule(TERM_LIST(
        `p:cm_program`, `model_ty:cm_type`), cm_patch_store);
    thm capacity_fact = assume_rule(
        `ilength (done:(tvm_inst)list) +
           ilength (cm_store_code (model_ty:cm_type)) <= (capacity:int)`);
    cm_open_resolved_emitter();
    cm_prepare_resolved_fragment(fragment, fragment,
                                 fragment_patch, capacity_fact);
    cm_expose_core_fragment(fragment);
  }
  [[cst::where(`tail`, `[]:(tvm_inst)list`)]]
  cm_emit_store(emitter, ty);
  [[cst::proof]] {
    term fragment = `cm_store_code (model_ty:cm_type)`;
    thm fragment_patch = specl_rule(TERM_LIST(
        `p:cm_program`, `model_ty:cm_type`), cm_patch_store);
    cm_finish_resolved_fragment(fragment, fragment, fragment_patch);
  }
}

void cm_emit_resolved_fp_address(struct cm_emitter *emitter,
                                 long long offset)
    [[cst::param(`p:cm_program`, `done:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ilength done +
              ilength (cm_fp_relative_address_code offset) <= capacity) **
       cm_resolved_emitter_rep p emitter out capacity done`)]]
    [[cst::ensure(
      `cm_resolved_emitter_rep p emitter out capacity
         (done ++ cm_fp_relative_address_code offset)`)]]
{
  [[cst::proof]] {
    term fragment =
        `cm_fp_relative_address_code (offset__pre:int)`;
    thm fragment_patch = specl_rule(TERM_LIST(
        `p:cm_program`, `offset__pre:int`), cm_patch_fp_address);
    thm capacity_fact = assume_rule(
        `ilength (done:(tvm_inst)list) +
           ilength (cm_fp_relative_address_code (offset__pre:int)) <=
         (capacity:int)`);
    cm_open_resolved_emitter();
    cm_prepare_resolved_fragment(fragment, fragment,
                                 fragment_patch, capacity_fact);
    cm_expose_core_fragment(fragment);
  }
  [[cst::where(`tail`, `[]:(tvm_inst)list`)]]
  cm_emit_fp_address(emitter, offset);
  [[cst::proof]] {
    term fragment =
        `cm_fp_relative_address_code (offset__pre:int)`;
    thm fragment_patch = specl_rule(TERM_LIST(
        `p:cm_program`, `offset__pre:int`), cm_patch_fp_address);
    cm_finish_resolved_fragment(fragment, fragment, fragment_patch);
  }
}

void cm_emit_resolved_temp_store(struct cm_function *fn, int temp,
                                 struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `fid:int`,
                 `structs:(cm_struct_d)list`, `body:int`, `next:int`,
                 `done:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= temp) **
       fact(structs == cm_program_structs p) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       fact(ilength done + ilength (cm_temp_store_code p fid temp) <=
              capacity) **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_rep p emitter out capacity done`)]]
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
       cm_resolved_emitter_rep p emitter out capacity
         (done ++ cm_temp_store_code p fid temp)`)]]
{
  [[cst::proof]] {
    term fragment =
        `cm_temp_store_code (p:cm_program) (fid:int) (temp__pre:int)`;
    thm fragment_patch = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `temp__pre:int`),
        cm_patch_temp_store);
    thm capacity_fact = assume_rule(
        `ilength (done:(tvm_inst)list) +
           ilength
             (cm_temp_store_code (p:cm_program) (fid:int)
               (temp__pre:int)) <=
         (capacity:int)`);
    cm_open_resolved_emitter();
    cm_prepare_resolved_fragment(fragment, fragment,
                                 fragment_patch, capacity_fact);
    cm_expose_core_fragment(fragment);
  }
  [[cst::where(`tail`, `[]:(tvm_inst)list`)]]
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`fid`, `(fid:int)`)]]
  [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
  [[cst::where(`body`, `(body:int)`)]]
  [[cst::where(`next`, `(next:int)`)]]
  [[cst::where(`out`, `(out:int)`)]]
  [[cst::where(`capacity`, `(capacity:int)`)]]
  cm_emit_temp_store(fn, temp, emitter);
  [[cst::proof]] {
    term fragment =
        `cm_temp_store_code (p:cm_program) (fid:int) (temp__pre:int)`;
    thm fragment_patch = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `temp__pre:int`),
        cm_patch_temp_store);
    cm_finish_resolved_fragment(fragment, fragment, fragment_patch);
  }
}

void cm_emit_resolved_temp_load(struct cm_function *fn, int temp,
                                struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `fid:int`,
                 `structs:(cm_struct_d)list`, `body:int`, `next:int`,
                 `done:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= temp) **
       fact(structs == cm_program_structs p) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       fact(ilength done + ilength (cm_temp_load_code p fid temp) <=
              capacity) **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_rep p emitter out capacity done`)]]
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
       cm_resolved_emitter_rep p emitter out capacity
         (done ++ cm_temp_load_code p fid temp)`)]]
{
  [[cst::proof]] {
    term fragment =
        `cm_temp_load_code (p:cm_program) (fid:int) (temp__pre:int)`;
    thm fragment_patch = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `temp__pre:int`),
        cm_patch_temp_load);
    thm capacity_fact = assume_rule(
        `ilength (done:(tvm_inst)list) +
           ilength
             (cm_temp_load_code (p:cm_program) (fid:int)
               (temp__pre:int)) <=
         (capacity:int)`);
    cm_open_resolved_emitter();
    cm_prepare_resolved_fragment(fragment, fragment,
                                 fragment_patch, capacity_fact);
    cm_expose_core_fragment(fragment);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`fid`, `(fid:int)`)]]
  [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
  [[cst::where(`body`, `(body:int)`)]]
  [[cst::where(`next`, `(next:int)`)]]
  [[cst::where(`out`, `(out:int)`)]]
  [[cst::where(`capacity`, `(capacity:int)`)]]
  [[cst::where(`tail`, `[]:(tvm_inst)list`)]]
  cm_emit_temp_load(fn, temp, emitter);
  [[cst::proof]] {
    term fragment =
        `cm_temp_load_code (p:cm_program) (fid:int) (temp__pre:int)`;
    thm fragment_patch = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `temp__pre:int`),
        cm_patch_temp_load);
    cm_finish_resolved_fragment(fragment, fragment, fragment_patch);
  }
}
