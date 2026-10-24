#include "cmc_concrete_patch_calls.h"
#include "userlib/array.h"
#include "userlib/pure_lists.h"

#require "cmc_concrete_function_pc_total.c"
#require "userlib/array.c"
#require "userlib/pure_lists.c"

PROOF thm cm_patch_tail_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_patch_tail ([]:(tvm_inst)list) == ([]:(tvm_inst)list)) /\
     (!(head:tvm_inst) (rest:(tvm_inst)list).
        cm_patch_tail (head :: rest) == rest)`);
PROOF int _cm_patch_tail_export =
    cst_add_const_to_header(`cm_patch_tail`);

PROOF static thm cm_patch_prove_ilength_zero_nil(void) {
  gnode root = gnode_new_with_ccl(
      `!(code:(tvm_inst)list). ilength code == 0i ==> code == []`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(leaf,
      ispec_rule(`code:(tvm_inst)list`,
        get_theorem_by_name("list_CASES")), "Hshape");
  ACCEPT_TAC(cases[0], assume_rule(
      `(code:(tvm_inst)list) == ([]:(tvm_inst)list)`));
  gnode cons = ASMP_EXISTS_TAC(cases[1], "Hshape", "head");
  cons = ASMP_EXISTS_TAC(cons, "Hshape", "rest");
  thm zero = conv_rule(rewrite_conv(THM_LIST(
      assume_rule(
        `(code:(tvm_inst)list) ==
         (head:tvm_inst) :: (rest:(tvm_inst)list)`),
      get_theorem_by_name("ILENGTH_DEF"))),
      assume_rule(`ilength (code:(tvm_inst)list) == 0i`));
  thm nonnegative = ispec_rule(`rest:(tvm_inst)list`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  CONTR_TAC(cons, mp_rule(mp_rule(int_arith_rule(
      `1i + ilength (rest:(tvm_inst)list) == 0i ==>
       0i <= ilength rest ==> F`), zero), nonnegative));
  return gnode_prove(root);
}
PROOF static thm cm_patch_ilength_zero_nil =
    cm_patch_prove_ilength_zero_nil();


PROOF static thm cm_patch_nonempty_shape_slrule(const thm nonempty) {
  term code = `raw:(tvm_inst)list`;
  term head = `HD (raw:(tvm_inst)list)`;
  term rest = `TL (raw:(tvm_inst)list)`;
  term opcode = `tvm_inst_op (HD (raw:(tvm_inst)list))`;
  term immediate = `tvm_inst_imm (HD (raw:(tvm_inst)list))`;
  thm list_shape = mp_rule(
      ispec_rule(code, get_theorem_by_name("CONS_HD_TL")), nonempty);
  thm rebuilt_head = spec_rule(head, get_tvm_inst_reconstruct());
  thm rebuilt_list = mk_comb_rule(mk_comb_rule(
      refl_rule(`CONS:tvm_inst->(tvm_inst)list->(tvm_inst)list`),
      rebuilt_head), refl_rule(rest));
  thm shape = trans_rule(list_shape, sym_rule(rebuilt_list));
  thm introduced = conv_rule(
      pure_rewrite_conv(THM_LIST(sl_sep_emp_right())),
      intro_fact_slrule(shape, refl_slrule(`emp`)));
  term rest_exists =
      `exists rest_:(tvm_inst)list.
         fact((raw:(tvm_inst)list) ==
              TVMInst (tvm_inst_op (HD raw))
                (tvm_inst_imm (HD raw)) :: rest_)`;
  term immediate_exists =
      `exists model_imm_:int. exists rest_:(tvm_inst)list.
         fact((raw:(tvm_inst)list) ==
              TVMInst (tvm_inst_op (HD raw)) model_imm_ :: rest_)`;
  term all_exist =
      `exists opcode_:tvm_opcode. exists model_imm_:int.
       exists rest_:(tvm_inst)list.
         fact((raw:(tvm_inst)list) ==
              TVMInst opcode_ model_imm_ :: rest_)`;
  introduced = exists_slrule(rest_exists, rest, introduced);
  introduced = exists_slrule(immediate_exists, immediate, introduced);
  return exists_slrule(all_exist, opcode, introduced);
}

PROOF static thm cm_patch_prove_rep_imms_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(code:(tvm_inst)list).
         ilength (cm_rep_imms code) == ilength code`);
  gnode_list cases = INDUCT_TAC(root, `code:(tvm_inst)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        get_cm_rep_imms_def(), get_theorem_by_name("ILENGTH_DEF")));
  }
  return gnode_prove(root);
}
PROOF static thm cm_patch_rep_imms_length =
    cm_patch_prove_rep_imms_length();

PROOF static thm cm_patch_rep_ops_cons(const thm shape) {
  thm lifted = ap_term_rule(
      `cm_rep_ops:(tvm_inst)list->(int)list`, shape);
  return trans_rule(lifted, apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_rep_ops_def(), get_tvm_inst_op_def())),
      rhs_of(lifted)));
}

PROOF static thm cm_patch_rep_imms_cons(const thm shape) {
  thm lifted = ap_term_rule(
      `cm_rep_imms:(tvm_inst)list->(int)list`, shape);
  return trans_rule(lifted, apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_rep_imms_def(), get_tvm_inst_imm_def())),
      rhs_of(lifted)));
}

PROOF static thm cm_patch_ilength_cons(const thm shape) {
  thm lifted = ap_term_rule(
      `ilength:(tvm_inst)list->int`, shape);
  return trans_rule(lifted, apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
      rhs_of(lifted)));
}

PROOF static thm cm_patch_resolved_ops_cons(
    const term program, const thm shape) {
  thm lifted = beta_norm(ap_term_rule(
      `\code:(tvm_inst)list.
         cm_rep_ops (cm_patch_code (p:cm_program) code)`,
      shape));
  lifted = inst_rule(TERM_PAIR_LIST(
      (term_pair){program, `p:cm_program`}), lifted);
  return trans_rule(lifted, apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_patch_code_def, cm_patch_inst_def,
        get_cm_rep_ops_def(), get_tvm_inst_op_def())),
      rhs_of(lifted)));
}

PROOF static thm cm_patch_resolved_imms_cons(
    const term program, const thm shape) {
  thm lifted = beta_norm(ap_term_rule(
      `\code:(tvm_inst)list.
         cm_rep_imms (cm_patch_code (p:cm_program) code)`,
      shape));
  lifted = inst_rule(TERM_PAIR_LIST(
      (term_pair){program, `p:cm_program`}), lifted);
  return trans_rule(lifted, apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_patch_code_def, get_cm_rep_imms_def())),
      rhs_of(lifted)));
}


PROOF static thm cm_patch_split_array(
    const term base, const term ty, const term length,
    const term head, const term tail, const thm whole_model,
    const thm array_def, const thm positive) {
  thm split = mp_rule(specl_rule(TERM_LIST(
      base, ty, length, head, tail),
      get_theorem_by_name("array_at_split_first")), positive);
  return conv_rule(rewrite_conv(THM_LIST(
      sym_rule(whole_model), gsym_rule(array_def))), split);
}

PROOF static thm cm_patch_merge_array(
    const term base, const term ty, const term length,
    const term head, const term tail, const thm whole_model,
    const thm array_def) {
  term length_variable = `patch_length:int`;
  thm merged = specl_rule(TERM_LIST(
      base, ty, `patch_length - 1i`, head, tail),
      get_theorem_by_name("array_at_merge_first"));
  thm count = int_arith_rule(
      `(patch_length - 1i) + 1i == patch_length`);
  thm result = conv_rule(rewrite_conv(THM_LIST(
      count, sym_rule(whole_model), gsym_rule(array_def))), merged);
  return inst_rule(TERM_PAIR_LIST(
      (term_pair){length, length_variable}), result);
}

static void cmc_patch_code_arrays(
    struct cm_program *program, int *ops, long long *imms, int length)
    [[cst::param(`p:cm_program`, `raw:(tvm_inst)list`,
                 `functions_ptr:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_concrete_code_ready p <=> true) **
       fact(0i <= length) ** fact(length <= 2147483647i) **
       fact(length == ilength raw) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr (cm_program_functions p) **
       store_int_array ops length (cm_rep_ops raw) **
       store_int64_array imms length (cm_rep_imms raw)`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_concrete_code_ready p <=> true) **
       fact(0i <= length) ** fact(length <= 2147483647i) **
       fact(length == ilength raw) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr (cm_program_functions p) **
       store_int_array ops length (cm_rep_ops (cm_patch_code p raw)) **
       store_int64_array imms length
         (cm_rep_imms (cm_patch_code p raw))`)]]
{
  if (length == 0) {
    [[cst::proof]] {
      thm model_zero = trans_rule(sym_rule(assume_rule(
          `(length__pre:int) == ilength (raw:(tvm_inst)list)`)),
          assume_rule(`(length__pre:int) == 0i`));
      thm raw_nil = mp_rule(
          spec_rule(`raw:(tvm_inst)list`, cm_patch_ilength_zero_nil),
          model_zero);
      thm patch_identity = by_rewrite(
          `cm_patch_code (p:cm_program) (raw:(tvm_inst)list) == raw`,
          THM_LIST(raw_nil, cm_patch_code_def));
      thm ops_model = ap_term_rule(
          `cm_rep_ops:(tvm_inst)list->(int)list`,
          sym_rule(patch_identity));
      thm ops_store = beta_norm(ap_term_rule(
          `\values:(int)list.
             store_int_array (ops__pre:int) (length__pre:int) values`,
          ops_model));
      apply_hconv_st(eq2ent(ops_store));

      thm imms_model = ap_term_rule(
          `cm_rep_imms:(tvm_inst)list->(int)list`,
          sym_rule(patch_identity));
      thm imms_store = beta_norm(ap_term_rule(
          `\values:(int)list.
             store_int64_array (imms__pre:int)
               (length__pre:int) values`,
          imms_model));
      apply_hconv_st(eq2ent(imms_store));
    }
    return;
  };

  [[cst::proof]] {
    thm nonzero = assume_rule(`~((length__pre:int) == 0i)`);
    thm nonnegative = assume_rule(`0i <= (length__pre:int)`);
    thm positive = mp_rule(mp_rule(int_arith_rule(
        `0i <= (length__pre:int) ==>
         ~(length__pre == 0i) ==> length__pre >= 1i`),
        nonnegative), nonzero);
    add_fact_st(positive);
    add_fact_st(mp_rule(int_arith_rule(
        `(length__pre:int) >= 1i ==> 0i <= length__pre - 1i`),
        positive));
    add_fact_st(mp_rule(mp_rule(int_arith_rule(
        `(length__pre:int) >= 1i ==>
         length__pre <= 2147483647i ==>
         length__pre - 1i <= 2147483647i`),
        positive), assume_rule(`(length__pre:int) <= 2147483647i`)));

    thm raw_length = sym_rule(assume_rule(
        `(length__pre:int) == ilength (raw:(tvm_inst)list)`));
    thm assumed_nil = assume_rule(
        `(raw:(tvm_inst)list) == ([]:(tvm_inst)list)`);
    thm nil_length = conv_rule(rewrite_conv(THM_LIST(
        assumed_nil, get_theorem_by_name("ILENGTH_DEF"))), raw_length);
    thm raw_nonempty = not_intro(
        `(raw:(tvm_inst)list) == ([]:(tvm_inst)list)`,
        contra(nonzero, sym_rule(nil_length)));
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(
          cm_patch_nonempty_shape_slrule(raw_nonempty),
          TERM_LIST(`opcode_:tvm_opcode`, `model_imm_:int`,
                    `rest_:(tvm_inst)list`))));
    thm witnessed_shape = assume_rule(
        `(raw:(tvm_inst)list) ==
         TVMInst (opcode_:tvm_opcode) (model_imm_:int) ::
           (rest_:(tvm_inst)list)`);
    thm tail_model = by_rewrite(
        `cm_patch_tail (raw:(tvm_inst)list) ==
         (rest_:(tvm_inst)list)`,
        THM_LIST(witnessed_shape, cm_patch_tail_def));
    thm canonical_shape = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(tail_model))), witnessed_shape);
    add_fact_st(canonical_shape);
    forget_fact_st(
        `(raw:(tvm_inst)list) ==
         TVMInst (opcode_:tvm_opcode) (model_imm_:int) ::
           (rest_:(tvm_inst)list)`);
    thm raw_shape = assume_rule(
        `(raw:(tvm_inst)list) ==
         TVMInst (opcode_:tvm_opcode) (model_imm_:int) ::
           cm_patch_tail raw`);

    term concrete_opcode =
        `tvm_opcode_code (opcode_:tvm_opcode)`;

    thm ops_model = cm_patch_rep_ops_cons(raw_shape);
    thm imms_model = cm_patch_rep_imms_cons(raw_shape);
    add_fact_st(ops_model);
    add_fact_st(imms_model);

    thm cons_length = cm_patch_ilength_cons(raw_shape);
    thm length_expanded = trans_rule(
        sym_rule(raw_length), cons_length);
    thm tail_length = mp_rule(int_arith_rule(mk_imp(
        concl(length_expanded),
        `(length__pre:int) - 1i ==
         ilength (cm_patch_tail (raw:(tvm_inst)list))`)),
        length_expanded);
    add_fact_st(tail_length);

    apply_hconv_st(cm_patch_split_array(
        `ops__pre:int`, `Tint`, `length__pre:int`, concrete_opcode,
        `cm_rep_ops (cm_patch_tail (raw:(tvm_inst)list))`,
        ops_model, get_theorem_by_name("store_int_array_def"),
        positive));
    apply_hconv_st(cm_patch_split_array(
        `imms__pre:int`, `Tint64`, `length__pre:int`,
        `model_imm_:int`,
        `cm_rep_imms (cm_patch_tail (raw:(tvm_inst)list))`,
        imms_model, get_theorem_by_name("store_int64_array_def"),
        positive));
  }

  int op = *ops;
  long long immediate = *imms;
  int *remaining_ops = ops + 1;
  long long *remaining_imms = imms + 1;
  int remaining_length = length - 1;
  [[cst::proof]] {
    thm ops_pointer = int_arith_rule(
        `(ops__pre:int) + 1i * sizeof Tint ==
         ops__pre + sizeof Tint`);
    thm ops_cell = eq2ent(mk_comb_rule(
        refl_rule(`data_at (remaining_ops__addr:addr) Tptr`),
        ops_pointer));
    cst_set_symbolic_state(local_apply(
        cst_get_symbolic_state(), ops_cell));

    thm imms_pointer = int_arith_rule(
        `(imms__pre:int) + 1i * sizeof Tint64 ==
         imms__pre + sizeof Tint64`);
    thm imms_cell = eq2ent(mk_comb_rule(
        refl_rule(`data_at (remaining_imms__addr:addr) Tptr`),
        imms_pointer));
    cst_set_symbolic_state(local_apply(
        cst_get_symbolic_state(), imms_cell));
  }
  if (op == CMC_OP_CALL) {
    int pc = cmc_function_pc_total(program, immediate);
    *imms = pc;
    [[cst::proof]] {
      term patched =
          `tvm_inst_imm
            (cm_patch_inst (p:cm_program)
              (TVMInst (opcode_:tvm_opcode) (model_imm_:int)))`;
      thm branch_value = by_rewrite(mk_eq(
          `cm_function_pc (p:cm_program) (model_imm_:int)`,
          patched), THM_LIST(cm_patch_inst_def,
            get_tvm_inst_op_def(), get_tvm_inst_imm_def(),
            assume_rule(
              `tvm_opcode_code (opcode_:tvm_opcode) == 22i`)));
      thm cell_value = trans_rule(assume_rule(
          `(retval:int) ==
           cm_function_pc (p:cm_program) (model_imm_:int)`),
          branch_value);
      add_fact_st(cell_value);
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `imms__pre:addr`,
          `retval:int`, patched));
      forget_fact_st(
          `(retval:int) ==
           tvm_inst_imm
             (cm_patch_inst (p:cm_program)
               (TVMInst (opcode_:tvm_opcode) (model_imm_:int)))`);
      forget_fact_st(
          `(retval:int) ==
           cm_function_pc (p:cm_program) (model_imm_:int)`);
      forget_fact_st(`cm_i32_code_count (retval:int) <=> true`);
      forget_fact_st(
          `tvm_opcode_code (opcode_:tvm_opcode) == 22i`);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`raw`,
        `cm_patch_tail (raw:(tvm_inst)list)`)]]
    [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
    cmc_patch_code_arrays(
        program, remaining_ops, remaining_imms, remaining_length);
  } else {
    [[cst::proof]] {
      term patched =
          `tvm_inst_imm
            (cm_patch_inst (p:cm_program)
              (TVMInst (opcode_:tvm_opcode) (model_imm_:int)))`;
      thm branch_value = by_rewrite(mk_eq(
          `model_imm_:int`, patched), THM_LIST(cm_patch_inst_def,
            get_tvm_inst_op_def(), get_tvm_inst_imm_def(),
            assume_rule(
              `~(tvm_opcode_code (opcode_:tvm_opcode) == 22i)`)));
      add_fact_st(branch_value);
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `imms__pre:addr`,
          `model_imm_:int`, patched));
      forget_fact_st(
          `(model_imm_:int) ==
           tvm_inst_imm
             (cm_patch_inst (p:cm_program)
               (TVMInst (opcode_:tvm_opcode) model_imm_))`);
      forget_fact_st(
          `~(tvm_opcode_code (opcode_:tvm_opcode) == 22i)`);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`raw`,
        `cm_patch_tail (raw:(tvm_inst)list)`)]]
    [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
    cmc_patch_code_arrays(
        program, remaining_ops, remaining_imms, remaining_length);
  };

  [[cst::proof]] {
    thm raw_shape = assume_rule(
        `(raw:(tvm_inst)list) ==
         TVMInst (opcode_:tvm_opcode) (model_imm_:int) ::
           cm_patch_tail raw`);
    term concrete_opcode =
        `tvm_opcode_code (opcode_:tvm_opcode)`;
    term patched_immediate =
        `tvm_inst_imm
          (cm_patch_inst (p:cm_program)
            (TVMInst (opcode_:tvm_opcode) (model_imm_:int)))`;
    thm patched_ops_model = cm_patch_resolved_ops_cons(
        `p:cm_program`, raw_shape);
    thm patched_imms_model = cm_patch_resolved_imms_cons(
        `p:cm_program`, raw_shape);
    add_fact_st(patched_ops_model);
    add_fact_st(patched_imms_model);

    apply_hconv_st(cm_patch_merge_array(
        `ops__pre:int`, `Tint`, `length__pre:int`, concrete_opcode,
        `cm_rep_ops (cm_patch_code (p:cm_program)
          (cm_patch_tail (raw:(tvm_inst)list)))`,
        patched_ops_model,
        get_theorem_by_name("store_int_array_def")));
    apply_hconv_st(cm_patch_merge_array(
        `imms__pre:int`, `Tint64`, `length__pre:int`, patched_immediate,
        `cm_rep_imms (cm_patch_code (p:cm_program)
          (cm_patch_tail (raw:(tvm_inst)list)))`,
        patched_imms_model,
        get_theorem_by_name("store_int64_array_def")));
  }
}

void cmc_patch_resolved_calls(struct cm_program *program,
                              struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `resolved:(tvm_inst)list`,
                 `functions_ptr:int`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_concrete_code_ready p <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr (cm_program_functions p) **
       cm_resolved_emitter_rep p emitter out capacity resolved`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_concrete_code_ready p <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr (cm_program_functions p) **
       cm_emitter_rep emitter out capacity
         (cm_rep_ops resolved) (cm_rep_imms resolved)`)]]
{
  [[cst::proof]] {
    thm resolved_view = apply_conversion(
        pure_rewrite_conv(THM_LIST(cm_resolved_emitter_rep_def)),
        `cm_resolved_emitter_rep (p:cm_program) (emitter__pre:int)
          (out:int) (capacity:int) (resolved:(tvm_inst)list)`);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(eq2ent(resolved_view),
          TERM_LIST(`raw_prefix_:(tvm_inst)list`))));
    thm emitter_view = apply_conversion(
        pure_rewrite_conv(THM_LIST(cm_emitter_rep_def)),
        `cm_emitter_rep (emitter__pre:int) (out:int) (capacity:int)
          (cm_rep_ops (raw_prefix_:(tvm_inst)list))
          (cm_rep_imms raw_prefix_)`);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(eq2ent(emitter_view),
          TERM_LIST(`ops_:int`, `imms_:int`))));
  }

  struct cm_output *output = emitter->output;
  int length = emitter->pc;
  int *ops = output->ops;
  long long *imms = output->imms;

  [[cst::proof]] {
    add_data_at_range_st(
        `field_addr (out:int) Tcm_output Fcode_capacity`,
        `Tint`, `capacity:int`);
    thm raw_ops_length = spec_rule(
        `raw_prefix_:(tvm_inst)list`, cm_rep_ops_length);
    add_fact_st(raw_ops_length);
    add_fact_st(conv_rule(rewrite_conv(THM_LIST(raw_ops_length)),
        assume_rule(
          `0i <= ilength (cm_rep_ops
            (raw_prefix_:(tvm_inst)list))`)));
    thm raw_at_most_capacity = conv_rule(
        rewrite_conv(THM_LIST(raw_ops_length)), assume_rule(
          `ilength (cm_rep_ops (raw_prefix_:(tvm_inst)list)) <=
           (capacity:int)`));
    thm capacity_upper = assume_rule(
        `(capacity:int) <= 2147483647i`);
    add_fact_st(mp_rule(mp_rule(int_arith_rule(
        `ilength (raw_prefix_:(tvm_inst)list) <= (capacity:int) ==>
         capacity <= 2147483647i ==>
         ilength raw_prefix_ <= 2147483647i`),
        raw_at_most_capacity), capacity_upper));
  }

  cmc_patch_code_arrays(program, ops, imms, length);

  [[cst::proof]] {
    thm patch_model = assume_rule(
        `cm_patch_code (p:cm_program)
           (raw_prefix_:(tvm_inst)list) ==
         (resolved:(tvm_inst)list)`);
    thm ops_model = ap_term_rule(
        `cm_rep_ops:(tvm_inst)list->(int)list`, patch_model);
    thm imms_model = ap_term_rule(
        `cm_rep_imms:(tvm_inst)list->(int)list`, patch_model);
    substitute_st(ops_model);
    substitute_st(imms_model);

    thm resolved_ops_length = spec_rule(
        `resolved:(tvm_inst)list`, cm_rep_ops_length);
    thm resolved_imms_length = spec_rule(
        `resolved:(tvm_inst)list`, cm_patch_rep_imms_length);
    thm lengths_equal = trans_rule(resolved_ops_length,
        sym_rule(resolved_imms_length));
    add_fact_st(lengths_equal);

    thm patch_length = specl_rule(TERM_LIST(
        `p:cm_program`, `raw_prefix_:(tvm_inst)list`),
        cm_patch_code_length);
    thm resolved_length = trans_rule(sym_rule(
        ap_term_rule(`ilength:(tvm_inst)list->int`, patch_model)),
        patch_length);
    thm ops_to_raw = trans_rule(resolved_ops_length, resolved_length);
    thm raw_ops_length = sym_rule(spec_rule(
        `raw_prefix_:(tvm_inst)list`, cm_rep_ops_length));
    thm new_to_old = trans_rule(ops_to_raw, raw_ops_length);
    add_fact_st(conv_rule(rewrite_conv(THM_LIST(
        sym_rule(new_to_old))), assume_rule(
          `0i <= ilength (cm_rep_ops
            (raw_prefix_:(tvm_inst)list))`)));
    add_fact_st(conv_rule(rewrite_conv(THM_LIST(
        sym_rule(new_to_old))), assume_rule(
          `ilength (cm_rep_ops (raw_prefix_:(tvm_inst)list)) <=
           (capacity:int)`)));
    rewrite_st(THM_LIST(sym_rule(new_to_old)));

    term subject =
        `cm_emitter_rep (emitter__pre:int) (out:int) (capacity:int)
          (cm_rep_ops (resolved:(tvm_inst)list))
          (cm_rep_imms resolved)`;
    thm folded = apply_conversion(
        pure_rewrite_conv(THM_LIST(cm_emitter_rep_def)), subject);
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
    introduced = exists_slrule(existential, `ops_:int`, introduced);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        trans_slrule(introduced, eq2ent(sym_rule(folded)))));
  }
}
