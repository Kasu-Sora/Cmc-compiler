#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_stack_annotations.h"
#require "cmc_stack_annotations.c"
#include "cmc_stack_local_core.h"

PROOF static size_t _cmc_stack_local_core_axioms_before = vector_size(get_all_axioms());

/* Local certificate algebra.  Fallthrough uses the remaining annotation
 * stream; absolute control-flow edges use target.  This form composes over
 * generated fragments and is projected to cm_stack_edges_from below. */
PROOF thm cm_local_next_def = new_fun_definition(
    `cm_local_next (rest:(int)list) (height:int) : bool =
       (~(rest == []) && HD rest == height)`);
PROOF thm cm_local_head_ok_def = new_fun_definition(
    `cm_local_head_ok (target:int->int) (inst:tvm_inst)
       (height:int) (rest:(int)list) : bool =
       (let op = tvm_inst_op inst in
        let imm = tvm_inst_imm inst in
        if op == TVMPushOp
        then cm_local_next rest (height + 1i)
        else if op == TVMPopOp
        then 1i <= height &&
             cm_local_next rest (height - 1i)
        else if op == TVMDupOp
        then 1i <= height &&
             cm_local_next rest (height + 1i)
        else if op == TVMSwapOp
        then 2i <= height && cm_local_next rest height
        else if op == TVMLoadOp || op == TVMLoadBOp
        then 1i <= height && cm_local_next rest height
        else if op == TVMStoreOp || op == TVMStoreBOp
        then 2i <= height &&
             cm_local_next rest (height - 2i)
        else if op == TVMAddOp || op == TVMSubOp ||
                op == TVMMulOp || op == TVMDivOp ||
                op == TVMModOp || op == TVMEqOp ||
                op == TVMNeOp || op == TVMLtOp ||
                op == TVMLeOp || op == TVMGtOp ||
                op == TVMGeOp
        then 2i <= height &&
             cm_local_next rest (height - 1i)
        else if op == TVMJmpOp
        then target imm == height
        else if op == TVMJzOp || op == TVMJnzOp
        then 1i <= height && target imm == height - 1i &&
             cm_local_next rest (height - 1i)
        else if op == TVMCallOp
        then target imm == height && cm_local_next rest 1i
        else if op == TVMRetOp
        then height == 1i
        else if op == TVMGetcOp
        then cm_local_next rest (height + 1i)
        else if op == TVMPutcOp || op == TVMPutiOp
        then 1i <= height &&
             cm_local_next rest (height - 1i)
        else height == 1i)`);
PROOF thm cm_local_codegen_ok_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p target annotations.
       cm_local_codegen_ok (p:cm_program) (target:int->int)
         ([]:(tvm_inst)list) (annotations:(int)list) =
       (annotations == [])) &&
     (!p target inst rest annotations.
       cm_local_codegen_ok (p:cm_program) (target:int->int)
         ((inst:tvm_inst) :: (rest:(tvm_inst)list))
         (annotations:(int)list) =
       (~(annotations == []) &&
        0i <= HD annotations &&
        cm_local_head_ok target inst (HD annotations)
          (TL annotations) &&
        (tvm_inst_op inst == TVMCallOp ==>
         ?fid.
           0i <= fid &&
           fid < ilength (cm_program_functions p) &&
           tvm_inst_imm inst == cm_function_pc p fid &&
           HD annotations ==
             ilength (cm_function_params
               (inth fid (cm_program_functions p)))) &&
        cm_local_codegen_ok p target rest (TL annotations)))`);
PROOF thm cm_height_stream_def = new_fun_definition(
    `cm_height_stream (target:int->int) (pc:int)
       (annotations:(int)list) : bool =
       (!(i:int).
          0i <= i ==> i < ilength annotations ==>
          target (pc + i) == inth i annotations)`);
PROOF thm cm_function_target_heights_def = new_fun_definition(
    `cm_function_target_heights (p:cm_program)
       (target:int->int) : bool =
       (!(fid:int).
          0i <= fid ==> fid < ilength (cm_program_functions p) ==>
          target (cm_function_pc p fid) ==
            ilength (cm_function_params
              (inth fid (cm_program_functions p))))`);

PROOF static thm cm_prove_height_stream_tail(void) {
  gnode root = gnode_new_with_ccl(
      `!(target:int->int) pc height rest.
         cm_height_stream target pc
           ((height:int) :: (rest:(int)list)) ==>
         cm_height_stream target (pc + 1i) rest`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode opened = CONV_TAC(leaf,
      pure_rewrite_conv(THM_LIST(cm_height_stream_def)));
  gnode body = AUTO_INTROS_TAC(opened);
  thm stream = pure_rewrite_rule(
      THM_LIST(cm_height_stream_def),
      assume_rule(
        `cm_height_stream (target:int->int) (pc:int)
           ((height:int) :: (rest:(int)list))`));
  thm lower = assume_rule(`0i <= (i:int)`);
  thm upper = assume_rule(`(i:int) < ilength (rest:(int)list)`);
  thm shifted_lower = mp_rule(
      int_arith_rule(mk_imp(concl(lower), `0i <= 1i + (i:int)`)),
      lower);
  thm cons_length = apply_conversion(
      rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
      `ilength ((height:int) :: (rest:(int)list))`);
  thm shifted_upper = mp_rule(int_arith_rule(mk_imp(
      mk_conj(concl(upper),
        `ilength ((height:int) :: (rest:(int)list)) ==
         1i + ilength rest`),
      `1i + (i:int) <
       ilength ((height:int) :: (rest:(int)list))`)),
      conj_rule(upper, cons_length));
  thm at_shift = mp_rule(mp_rule(
      spec_rule(`1i + (i:int)`, stream), shifted_lower),
      shifted_upper);
  thm suffix_index = mp_rule(ispecl_rule(TERM_LIST(
      `[(height:int)]`, `rest:(int)list`, `i:int`),
      cm_inth_append_right), lower);
  thm suffix_exact = pure_rewrite_rule(THM_LIST(
      get_theorem_by_name("ILENGTH_DEF"),
      get_theorem_by_name("APPEND"),
      int_arith_rule(`(1i + 0i) + (i:int) == 1i + i`)),
      suffix_index);
  thm pc_equal = int_arith_rule(
      `(pc:int) + (1i + (i:int)) == (pc + 1i) + i`);
  thm target_equal = beta_norm(ap_term_rule(
      `\address:int. (target:int->int) address`, pc_equal));
  thm result = trans_rule(sym_rule(target_equal),
      trans_rule(at_shift, suffix_exact));
  ACCEPT_TAC(body, result);
  return gnode_prove(root);
}
PROOF thm cm_height_stream_tail =
    cm_prove_height_stream_tail();

PROOF static thm cm_prove_stream_next_at(void) {
  gnode root = gnode_new_with_ccl(
      `!(heights:(int)list) (code:(tvm_inst)list) pc
         height rest next.
         cm_height_stream (\address:int. inth address heights) pc
           ((height:int) :: (rest:(int)list)) &&
         cm_local_next rest next ==>
         cm_stack_at code heights (pc + 1i) next`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list assumptions = AUTO_ASMP_DESTRUCT_TAC(leaf);
  leaf = assumptions[0];
  gnode_list rest_cases =
      CASES_TAC(leaf, `rest:(int)list`, "hrest");
  {
    thm empty = assume_rule(
        `(rest:(int)list) == ([]:(int)list)`);
    thm impossible = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          empty, cm_local_next_def, get_theorem_by_name("HD"))),
        assume_rule(`cm_local_next (rest:(int)list) (next:int)`));
    CONTR_TAC(rest_cases[0], impossible);
  }
  {
    gnode branch = rest_cases[1];
    thm rest_shape = assume_rule(
        `(rest:(int)list) ==
         ((a0:int) :: (a1:(int)list))`);
    thm stream = pure_rewrite_rule(
        THM_LIST(cm_height_stream_def),
        conv_rule(rewrite_conv(THM_LIST(rest_shape)),
          assume_rule(
            `cm_height_stream
               (\address:int. inth address (heights:(int)list))
               (pc:int)
               ((height:int) :: (rest:(int)list))`)));
    thm tail_nonnegative = ispec_rule(
        `a1:(int)list`, get_theorem_by_name("ILENGTH_NONNEG"));
    thm stream_length = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        `ilength
           ((height:int) :: ((a0:int) :: (a1:(int)list)))`);
    thm one_in_range = mp_rule(int_arith_rule(mk_imp(
        mk_conj(concl(tail_nonnegative), concl(stream_length)),
        `1i <
         ilength
           ((height:int) :: ((a0:int) :: (a1:(int)list)))`)),
        conj_rule(tail_nonnegative, stream_length));
    thm at_one = mp_rule(mp_rule(
        spec_rule(`1i`, stream), int_arith_rule(`0i <= 1i`)),
        one_in_range);
    thm suc_zero = apply_conversion(
        get_conversion_by_name("NUM_SUC_CONV"), `SUC 0`);
    thm nth_one = conv_rule(rewrite_conv(THM_LIST(suc_zero)),
        inst_rule(TERM_PAIR_LIST(
          (term_pair){`0`, `n:num`}),
          conjunct2_rule(get_theorem_by_name("NTH_DEF"))));
    thm at_one_reduced = beta_norm(at_one);
    thm local_one = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("INTH_DEF"),
          get_theorem_by_name("NUM_OF_INT_OF_NUM"),
          nth_one, get_theorem_by_name("NTH_DEF"))),
        `inth 1i
           ((height:int) :: ((a0:int) :: (a1:(int)list)))`);
    thm next_equal = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          rest_shape, cm_local_next_def,
          get_theorem_by_name("HD"))),
        assume_rule(
          `cm_local_next (rest:(int)list) (next:int)`));
    thm result = trans_rule(at_one_reduced,
        trans_rule(local_one, conjunct2_rule(next_equal)));
    gnode reduced = CONV_TAC(
        branch, rewrite_conv(THM_LIST(get_cm_stack_at_def())));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_stream_next_at = cm_prove_stream_next_at();

PROOF thm cm_matching_assumption(
    const gnode leaf, const term wanted) {
  labeled_term_list assumptions = goal_lasmps(leaf->g);
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    if (alpha_compare(assumptions[i].tm, wanted) == 0) {
      return assume_rule(assumptions[i].tm);
    }
  }
  ENSURE_COND(false, "required stack assumption is absent: %s in %s",
      cstr_term(wanted), cstr_gnode(leaf));
err:
  return empty_theorem;
}

PROOF static bool cm_has_conjunct(
    const term tree, const term wanted) {
  if (alpha_compare(tree, wanted) == 0) {
    return true;
  }
  if (!is_conj(tree)) {
    return false;
  }
  dest_conj_results parts = dest_conj(tree);
  return cm_has_conjunct(parts.tm1, wanted) ||
         cm_has_conjunct(parts.tm2, wanted);
}

PROOF thm cm_pick_conjunct(
    const thm fact, const term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) {
    return fact;
  }
  dest_conj_results parts = dest_conj(concl(fact));
  return cm_has_conjunct(parts.tm1, wanted)
      ? cm_pick_conjunct(conjunct1_rule(fact), wanted)
      : cm_pick_conjunct(conjunct2_rule(fact), wanted);
}

PROOF static thm cm_prove_local_head_sound(void) {
  gnode root = gnode_new_with_ccl(
      `!(heights:(int)list) (code:(tvm_inst)list) pc inst
         height rest.
         cm_height_stream (\address:int. inth address heights) pc
           ((height:int) :: (rest:(int)list)) &&
         cm_local_head_ok
           (\address:int. inth address heights)
           (inst:tvm_inst) height rest ==>
         cm_stack_head_ok code heights pc inst height`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list assumptions = AUTO_ASMP_DESTRUCT_TAC(leaf);
  leaf = assumptions[0];
  gnode_list inst_cases =
      CASES_TAC(leaf, `inst:tvm_inst`, "hinst");
  gnode_list opcode_cases =
      CASES_TAC(inst_cases[0], `a0:tvm_opcode`, "hop");
  for (size_t i = 0; i < vector_size(opcode_cases); ++i) {
    gnode normalized = CONV_WITH_ASMP_TAC(
        opcode_cases[i], reduce_rewrite_conv, THM_LIST(
          cm_local_head_ok_def, get_cm_stack_head_ok_def(),
          get_cm_stack_at_def(), get_tvm_inst_op_def(),
          get_tvm_inst_imm_def(),
          get_datatype_distinctness("tvm_opcode")));
    if (!IS_NULL(normalized->solved)) {
      continue;
    }
    labeled_term_list branch_assumptions =
        goal_lasmps(normalized->g);
    thm hinst = assume_rule(branch_assumptions[
        labeled_term_list_index(branch_assumptions, "hinst")].tm);
    thm hop = assume_rule(branch_assumptions[
        labeled_term_list_index(branch_assumptions, "hop")].tm);
    term local_app =
        `cm_local_head_ok
           (\address:int. inth address (heights:(int)list))
           (inst:tvm_inst) (height:int) (rest:(int)list)`;
    thm local = cm_matching_assumption(normalized, local_app);
    thm local_reduced = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          cm_local_head_ok_def, get_tvm_inst_op_def(),
          get_tvm_inst_imm_def(), hinst, hop,
          get_datatype_distinctness("tvm_opcode"))),
        local);
    term expected = empty_term;
    if (i == 0 || i == 2 || i == 24) {
      expected = `(height:int) + 1i`;
    } else if (i == 1 || (8 <= i && i <= 18) ||
               i == 20 || i == 21 || i == 25 || i == 26) {
      expected = `(height:int) - 1i`;
    } else if (i == 3 || i == 4 || i == 6) {
      expected = `height:int`;
    } else if (i == 5 || i == 7) {
      expected = `(height:int) - 2i`;
    } else if (i == 22) {
      expected = `1i`;
    }
    if (IS_NULL(expected)) {
      CONV_TAC(normalized,
          reduce_rewrite_conv(THM_LIST(local_reduced)));
      continue;
    }
    term next_app = mk_comb(mk_comb(
        `cm_local_next:(int)list->int->bool`,
        `rest:(int)list`), expected);
    thm next = cm_pick_conjunct(local_reduced, next_app);
    term stream_app =
        `cm_height_stream
           (\address:int. inth address (heights:(int)list))
           (pc:int)
           ((height:int) :: (rest:(int)list))`;
    thm stream = cm_matching_assumption(normalized, stream_app);
    thm next_at = mp_rule(specl_rule(TERM_LIST(
        `heights:(int)list`, `code:(tvm_inst)list`, `pc:int`,
        `height:int`, `rest:(int)list`, expected),
        cm_stream_next_at), conj_rule(stream, next));
    thm next_equal = pure_rewrite_rule(
        THM_LIST(get_cm_stack_at_def()), next_at);
    CONV_TAC(normalized, reduce_rewrite_conv(
        THM_LIST(local_reduced, next_equal)));
  }
  return gnode_prove(root);
}
PROOF thm cm_local_head_sound = cm_prove_local_head_sound();

PROOF static thm cm_prove_local_codegen_edges(void) {
  gnode root = gnode_new_with_ccl(
      `!(instructions:(tvm_inst)list).
         !(p:cm_program) (global_code:(tvm_inst)list)
           (global_heights:(int)list) pc annotations.
         cm_height_stream
           (\address:int. inth address global_heights) pc
           (annotations:(int)list) &&
         cm_local_codegen_ok p
           (\address:int. inth address global_heights)
           instructions annotations ==>
         cm_stack_edges_from global_code global_heights pc
           instructions annotations`);
  gnode_list cases =
      INDUCT_TAC(root, `instructions:(tvm_inst)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    gnode_list assumptions = AUTO_ASMP_DESTRUCT_TAC(leaf);
    leaf = assumptions[0];
    thm local = assume_rule(
        `cm_local_codegen_ok (p:cm_program)
           (\address:int. inth address
             (global_heights:(int)list))
           ([]:(tvm_inst)list) (annotations:(int)list)`);
    thm empty = pure_rewrite_rule(
        THM_LIST(cm_local_codegen_ok_def), local);
    gnode reduced = CONV_TAC(leaf,
        rewrite_conv(THM_LIST(get_cm_stack_edges_from_def())));
    ACCEPT_TAC(reduced, empty);
  }
  {
    gnode constructor_leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list assumptions =
        AUTO_ASMP_DESTRUCT_TAC(constructor_leaf);
    gnode leaf = assumptions[0];
    gnode_list annotation_cases =
        CASES_TAC(leaf, `annotations:(int)list`, "hannotations");
    {
      thm empty_shape = assume_rule(
          `(annotations:(int)list) == ([]:(int)list)`);
      thm local = assume_rule(
          `cm_local_codegen_ok (p:cm_program)
             (\address:int. inth address
               (global_heights:(int)list))
             ((a0:tvm_inst) :: (a1:(tvm_inst)list))
             (annotations:(int)list)`);
      thm impossible = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            empty_shape, cm_local_codegen_ok_def)),
          local);
      CONTR_TAC(annotation_cases[0], impossible);
    }
    {
      gnode branch = annotation_cases[1];
      term annotation_shape_term =
          `(annotations:(int)list) ==
           ((a0:int) :: (a1:(int)list))`;
      thm annotation_shape =
          cm_matching_assumption(branch, annotation_shape_term);
      dest_comb_results annotation_outer =
          dest_comb(rhs_of(annotation_shape));
      dest_comb_results annotation_inner =
          dest_comb(annotation_outer.tm1);
      term annotation_head = annotation_inner.tm2;
      term annotation_tail = annotation_outer.tm2;
      term stream_term =
          `cm_height_stream
             (\address:int. inth address
               (global_heights:(int)list))
             (pc:int) (annotations:(int)list)`;
      thm stream = conv_rule(rewrite_conv(THM_LIST(
          annotation_shape)),
          cm_matching_assumption(branch, stream_term));
      term local_term =
          `cm_local_codegen_ok (p:cm_program)
             (\address:int. inth address
               (global_heights:(int)list))
             ((a0:tvm_inst) :: (a1:(tvm_inst)list))
             (annotations:(int)list)`;
      thm local = conv_rule(rewrite_conv(THM_LIST(
          annotation_shape)),
          cm_matching_assumption(branch, local_term));
      thm local_parts = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            cm_local_codegen_ok_def,
            get_theorem_by_name("HD"),
            get_theorem_by_name("TL"))),
          local);
      thm nonnegative = cm_pick_conjunct(
          local_parts, `0i <= ${annotation_head:int}`);
      thm local_head = cm_pick_conjunct(
          local_parts,
          `cm_local_head_ok
             (\address:int. inth address
               (global_heights:(int)list))
             (a0:tvm_inst) ${annotation_head:int}
             ${annotation_tail:(int)list}`);
      thm local_tail = cm_pick_conjunct(
          local_parts,
          `cm_local_codegen_ok (p:cm_program)
             (\address:int. inth address
               (global_heights:(int)list))
             (a1:(tvm_inst)list)
             ${annotation_tail:(int)list}`);
      thm global_head = mp_rule(specl_rule(TERM_LIST(
          `global_heights:(int)list`,
          `global_code:(tvm_inst)list`, `pc:int`,
          `a0:tvm_inst`, annotation_head, annotation_tail),
          cm_local_head_sound), conj_rule(stream, local_head));
      thm tail_stream = mp_rule(specl_rule(TERM_LIST(
          `\address:int. inth address
             (global_heights:(int)list)`,
          `pc:int`, annotation_head, annotation_tail),
          cm_height_stream_tail), stream);
      term ih_term =
          `!(p:cm_program) (global_code:(tvm_inst)list)
             (global_heights:(int)list) pc annotations.
             cm_height_stream
               (\address:int. inth address global_heights) pc
               (annotations:(int)list) &&
             cm_local_codegen_ok p
               (\address:int. inth address global_heights)
               (a1:(tvm_inst)list) annotations ==>
             cm_stack_edges_from global_code global_heights pc
               a1 annotations`;
      thm ih = cm_matching_assumption(branch, ih_term);
      thm tail_edges = mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `global_code:(tvm_inst)list`,
          `global_heights:(int)list`, `(pc:int) + 1i`,
          annotation_tail), ih),
          conj_rule(tail_stream, local_tail));
      thm result = conj_rule(nonnegative,
          conj_rule(global_head, tail_edges));
      gnode reduced = CONV_TAC(branch,
          reduce_rewrite_conv(THM_LIST(
            annotation_shape, get_cm_stack_edges_from_def(),
            get_theorem_by_name("NOT_CONS_NIL"),
            get_theorem_by_name("HD"),
            get_theorem_by_name("TL"))));
      ACCEPT_TAC(reduced, result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_local_codegen_edges =
    cm_prove_local_codegen_edges();

PROOF static thm cm_prove_inth_cons_tail(void) {
  gnode root = gnode_new_with_ccl(
      `!(head:A) (tail:(A)list) i.
         1i <= i ==>
         inth i (head :: tail) == inth (i - 1i) tail`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm lower = assume_rule(`1i <= (i:int)`);
  thm shifted_lower = mp_rule(int_arith_rule(mk_imp(
      concl(lower), `0i <= (i:int) - 1i`)), lower);
  thm split = mp_rule(ispecl_rule(TERM_LIST(
      `[(head:A)]`, `tail:(A)list`, `(i:int) - 1i`),
      cm_inth_append_right), shifted_lower);
  thm split_reduced = pure_rewrite_rule(THM_LIST(
      get_theorem_by_name("ILENGTH_DEF"),
      get_theorem_by_name("APPEND")), split);
  thm index_equal = mp_rule(int_arith_rule(mk_imp(
      concl(lower),
      `(1i + 0i) + ((i:int) - 1i) == i`)), lower);
  thm lifted = beta_norm(ap_term_rule(
      `\index:int. inth index
         ((head:A) :: (tail:(A)list))`, index_equal));
  ACCEPT_TAC(leaf, trans_rule(sym_rule(lifted), split_reduced));
  return gnode_prove(root);
}
PROOF thm cm_inth_cons_tail = cm_prove_inth_cons_tail();

PROOF static thm cm_prove_function_entries_at(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list).
         !(p:cm_program) base index.
         0i <= index && index < ilength functions ==>
         inth index
           (cm_function_entries_from p functions base) ==
         cm_function_pc p (base + index)`);
  gnode_list cases =
      INDUCT_TAC(root, `functions:(cm_function_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm bounds = assume_rule(
        `0i <= (index:int) &&
         index < ilength ([]:(cm_function_d)list)`);
    thm reduced_bounds = pure_rewrite_rule(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF")), bounds);
    thm impossible = mp_rule(int_arith_rule(mk_imp(
        concl(reduced_bounds), `F`)), reduced_bounds);
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm bounds = assume_rule(
        `0i <= (index:int) &&
         index <
           ilength ((a0:cm_function_d) ::
             (a1:(cm_function_d)list))`);
    gnode_list index_cases =
        BOOL_CASES_TAC(leaf, `(index:int) == 0i`, "hindex");
    {
      gnode reduced = CONV_WITH_ASMP_TAC(
          index_cases[0], reduce_rewrite_conv, THM_LIST(
            cm_function_entries_from_def,
            get_theorem_by_name("INTH_DEF"),
            get_theorem_by_name("NUM_OF_INT_OF_NUM"),
            get_theorem_by_name("NTH_DEF")));
      if (IS_NULL(reduced->solved)) {
        thm zero = int_arith_rule(`(base:int) + 0i == base`);
        ACCEPT_TAC(reduced, beta_norm(ap_term_rule(
            `\fid:int. cm_function_pc (p:cm_program) fid`,
            sym_rule(zero))));
      }
    }
    {
      thm not_zero = assume_rule(`~((index:int) == 0i)`);
      thm reduced_bounds = pure_rewrite_rule(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF")), bounds);
      thm one_le = mp_rule(int_arith_rule(mk_imp(
          mk_conj(concl(reduced_bounds), concl(not_zero)),
          `1i <= (index:int)`)),
          conj_rule(reduced_bounds, not_zero));
      thm tail_bounds = mp_rule(int_arith_rule(mk_imp(
          mk_conj(concl(reduced_bounds), concl(not_zero)),
          `0i <= (index:int) - 1i &&
           index - 1i < ilength (a1:(cm_function_d)list)`)),
          conj_rule(reduced_bounds, not_zero));
      thm ih = assume_rule(
          `!(p:cm_program) base index.
             0i <= index &&
             index < ilength (a1:(cm_function_d)list) ==>
             inth index
               (cm_function_entries_from p a1 base) ==
             cm_function_pc p (base + index)`);
      thm ih_at = mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `(base:int) + 1i`,
          `(index:int) - 1i`), ih), tail_bounds);
      thm list_step = mp_rule(ispecl_rule(TERM_LIST(
          `cm_function_pc (p:cm_program) (base:int)`,
          `cm_function_entries_from p
             (a1:(cm_function_d)list) (base + 1i)`,
          `index:int`), cm_inth_cons_tail), one_le);
      thm fid_equal = int_arith_rule(
          `((base:int) + 1i) + ((index:int) - 1i) ==
           base + index`);
      thm rhs_equal = beta_norm(ap_term_rule(
          `\fid:int. cm_function_pc (p:cm_program) fid`,
          fid_equal));
      thm result = trans_rule(list_step,
          trans_rule(ih_at, rhs_equal));
      gnode reduced = CONV_TAC(index_cases[1],
          rewrite_conv(THM_LIST(cm_function_entries_from_def)));
      ACCEPT_TAC(reduced, result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_function_entries_at =
    cm_prove_function_entries_at();

PROOF static thm cm_prove_function_arities_at(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list) index.
         0i <= index && index < ilength functions ==>
         inth index (cm_function_arities functions) ==
         ilength (cm_function_params (inth index functions))`);
  gnode_list cases =
      INDUCT_TAC(root, `functions:(cm_function_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm bounds = assume_rule(
        `0i <= (index:int) &&
         index < ilength ([]:(cm_function_d)list)`);
    thm reduced_bounds = pure_rewrite_rule(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF")), bounds);
    thm impossible = mp_rule(int_arith_rule(mk_imp(
        concl(reduced_bounds), `F`)), reduced_bounds);
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm bounds = assume_rule(
        `0i <= (index:int) &&
         index <
           ilength ((a0:cm_function_d) ::
             (a1:(cm_function_d)list))`);
    gnode_list index_cases =
        BOOL_CASES_TAC(leaf, `(index:int) == 0i`, "hindex");
    {
      CONV_WITH_ASMP_TAC(index_cases[0],
          reduce_rewrite_conv, THM_LIST(
            cm_function_arities_def,
            get_theorem_by_name("INTH_DEF"),
            get_theorem_by_name("NUM_OF_INT_OF_NUM"),
            get_theorem_by_name("NTH_DEF")));
    }
    {
      thm not_zero = assume_rule(`~((index:int) == 0i)`);
      thm reduced_bounds = pure_rewrite_rule(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF")), bounds);
      thm one_le = mp_rule(int_arith_rule(mk_imp(
          mk_conj(concl(reduced_bounds), concl(not_zero)),
          `1i <= (index:int)`)),
          conj_rule(reduced_bounds, not_zero));
      thm tail_bounds = mp_rule(int_arith_rule(mk_imp(
          mk_conj(concl(reduced_bounds), concl(not_zero)),
          `0i <= (index:int) - 1i &&
           index - 1i < ilength (a1:(cm_function_d)list)`)),
          conj_rule(reduced_bounds, not_zero));
      thm ih = assume_rule(
          `!index.
             0i <= index &&
             index < ilength (a1:(cm_function_d)list) ==>
             inth index (cm_function_arities a1) ==
             ilength (cm_function_params (inth index a1))`);
      thm ih_at = mp_rule(spec_rule(
          `(index:int) - 1i`, ih), tail_bounds);
      thm arity_step = mp_rule(ispecl_rule(TERM_LIST(
          `ilength (cm_function_params (a0:cm_function_d))`,
          `cm_function_arities (a1:(cm_function_d)list)`,
          `index:int`), cm_inth_cons_tail), one_le);
      thm function_step = mp_rule(ispecl_rule(TERM_LIST(
          `a0:cm_function_d`, `a1:(cm_function_d)list`,
          `index:int`), cm_inth_cons_tail), one_le);
      thm params_step = beta_norm(ap_term_rule(
          `\f:cm_function_d.
             ilength (cm_function_params f)`, function_step));
      thm result = trans_rule(arity_step,
          trans_rule(ih_at, sym_rule(params_step)));
      gnode reduced = CONV_TAC(index_cases[1],
          rewrite_conv(THM_LIST(cm_function_arities_def)));
      ACCEPT_TAC(reduced, result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_function_arities_at =
    cm_prove_function_arities_at();

PROOF static thm cm_prove_function_arities_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list).
         ilength (cm_function_arities functions) ==
         ilength functions`);
  gnode_list cases =
      INDUCT_TAC(root, `functions:(cm_function_d)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        cm_function_arities_def,
        get_theorem_by_name("ILENGTH_DEF")));
  }
  return gnode_prove(root);
}
PROOF thm cm_function_arities_length =
    cm_prove_function_arities_length();

PROOF static thm cm_prove_local_call_listed(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (inst:tvm_inst) height.
         (tvm_inst_op inst == TVMCallOp ==>
          ?fid.
            0i <= fid &&
            fid < ilength (cm_program_functions p) &&
            tvm_inst_imm inst == cm_function_pc p fid &&
            height ==
              ilength (cm_function_params
                (inth fid (cm_program_functions p)))) ==>
         (tvm_inst_op inst == TVMCallOp ==>
          ?fid.
            0i <= fid &&
            fid < ilength (cm_codegen_function_entries p) &&
            tvm_inst_imm inst ==
              inth fid (cm_codegen_function_entries p) &&
            height ==
              inth fid (cm_codegen_function_arities p))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm source_rule = assume_rule(
      `tvm_inst_op (inst:tvm_inst) == TVMCallOp ==>
       ?fid.
         0i <= fid &&
         fid < ilength (cm_program_functions (p:cm_program)) &&
         tvm_inst_imm inst == cm_function_pc p fid &&
         (height:int) ==
           ilength (cm_function_params
             (inth fid (cm_program_functions p)))`);
  thm is_call = assume_rule(
      `tvm_inst_op (inst:tvm_inst) == TVMCallOp`);
  thm source = mp_rule(source_rule, is_call);
  thm body = assume_rule(
      `0i <= (fid:int) &&
       fid < ilength (cm_program_functions (p:cm_program)) &&
       tvm_inst_imm (inst:tvm_inst) == cm_function_pc p fid &&
       (height:int) ==
         ilength (cm_function_params
           (inth fid (cm_program_functions p)))`);
  thm lower = conjunct1_rule(body);
  thm rest1 = conjunct2_rule(body);
  thm upper = conjunct1_rule(rest1);
  thm rest2 = conjunct2_rule(rest1);
  thm immediate = conjunct1_rule(rest2);
  thm value_height = conjunct2_rule(rest2);
  thm bounds = conj_rule(lower, upper);
  thm entry_at = mp_rule(specl_rule(TERM_LIST(
      `cm_program_functions (p:cm_program)`, `p:cm_program`,
      `0i`, `fid:int`), cm_function_entries_at), bounds);
  thm entry_fid = int_arith_rule(`0i + (fid:int) == fid`);
  thm entry_pc = trans_rule(entry_at, beta_norm(ap_term_rule(
      `\index:int. cm_function_pc (p:cm_program) index`,
      entry_fid)));
  thm entries_def = beta_norm(ap_term_rule(
      `\entries:(int)list. inth (fid:int) entries`,
      cm_codegen_function_entries_def));
  thm listed_entry = trans_rule(entries_def, entry_pc);
  thm arity_at = mp_rule(specl_rule(TERM_LIST(
      `cm_program_functions (p:cm_program)`, `fid:int`),
      cm_function_arities_at), bounds);
  thm arities_def = beta_norm(ap_term_rule(
      `\arities:(int)list. inth (fid:int) arities`,
      cm_codegen_function_arities_def));
  thm listed_arity = trans_rule(arities_def, arity_at);
  thm entries_length = trans_rule(
      ap_term_rule(`ilength:(int)list->int`,
        cm_codegen_function_entries_def),
      trans_rule(specl_rule(TERM_LIST(
          `cm_program_functions (p:cm_program)`, `p:cm_program`,
          `0i`), cm_entries_arities_length),
        spec_rule(`cm_program_functions (p:cm_program)`,
          cm_function_arities_length)));
  thm listed_upper = mp_rule(int_arith_rule(mk_imp(
      mk_conj(concl(upper),
        `ilength (cm_codegen_function_entries (p:cm_program)) ==
         ilength (cm_program_functions p)`),
      `(fid:int) <
       ilength (cm_codegen_function_entries p)`)),
      conj_rule(upper, entries_length));
  thm listed_immediate = trans_rule(
      immediate, sym_rule(listed_entry));
  thm listed_height = trans_rule(
      value_height, sym_rule(listed_arity));
  thm listed_body = conj_rule(lower,
      conj_rule(listed_upper,
        conj_rule(listed_immediate, listed_height)));
  thm witness = exists_rule(
      `?fid.
         0i <= fid &&
         fid < ilength (cm_codegen_function_entries (p:cm_program)) &&
         tvm_inst_imm (inst:tvm_inst) ==
           inth fid (cm_codegen_function_entries p) &&
         (height:int) ==
           inth fid (cm_codegen_function_arities p)`,
      `fid:int`, listed_body);
  thm result = choose_rule(`fid:int`, source, witness);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_local_call_listed =
    cm_prove_local_call_listed();

PROOF static thm cm_prove_local_codegen_calls(void) {
  gnode root = gnode_new_with_ccl(
      `!(instructions:(tvm_inst)list).
         !(p:cm_program) (target:int->int) (obj:tvm_object)
           (heights:(int)list) pc annotations.
         cm_local_codegen_ok p target instructions
           (annotations:(int)list) ==>
         cm_stack_call_insts_from obj heights
           (cm_codegen_function_entries p)
           (cm_codegen_function_arities p) pc
           instructions annotations`);
  gnode_list cases =
      INDUCT_TAC(root, `instructions:(tvm_inst)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_stack_call_insts_from_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list annotation_cases =
        CASES_TAC(leaf, `annotations:(int)list`, "hannotations");
    {
      term local_term =
          `cm_local_codegen_ok (p:cm_program)
             (target:int->int)
             ((a0:tvm_inst) :: (a1:(tvm_inst)list))
             (annotations:(int)list)`;
      thm local = cm_matching_assumption(
          annotation_cases[0], local_term);
      thm empty_shape = cm_matching_assumption(
          annotation_cases[0],
          `(annotations:(int)list) == ([]:(int)list)`);
      thm impossible = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            empty_shape, cm_local_codegen_ok_def)),
          local);
      CONTR_TAC(annotation_cases[0], impossible);
    }
    {
      gnode branch = annotation_cases[1];
      labeled_term_list branch_assumptions =
          goal_lasmps(branch->g);
      thm annotation_shape = assume_rule(branch_assumptions[
          labeled_term_list_index(
            branch_assumptions, "hannotations")].tm);
      dest_comb_results annotation_outer =
          dest_comb(rhs_of(annotation_shape));
      dest_comb_results annotation_inner =
          dest_comb(annotation_outer.tm1);
      term annotation_head = annotation_inner.tm2;
      term annotation_tail = annotation_outer.tm2;
      term local_term =
          `cm_local_codegen_ok (p:cm_program)
             (target:int->int)
             ((a0:tvm_inst) :: (a1:(tvm_inst)list))
             (annotations:(int)list)`;
      thm local = conv_rule(rewrite_conv(THM_LIST(
          annotation_shape)),
          cm_matching_assumption(branch, local_term));
      thm local_parts = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            cm_local_codegen_ok_def,
            get_theorem_by_name("HD"),
            get_theorem_by_name("TL"))),
          local);
      term direct_call_term =
          `tvm_inst_op (a0:tvm_inst) == TVMCallOp ==>
           ?fid.
             0i <= fid &&
             fid < ilength (cm_program_functions (p:cm_program)) &&
             tvm_inst_imm a0 == cm_function_pc p fid &&
             ${annotation_head:int} ==
               ilength (cm_function_params
                 (inth fid (cm_program_functions p)))`;
      thm direct_call =
          cm_pick_conjunct(local_parts, direct_call_term);
      thm listed_call = mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `a0:tvm_inst`, annotation_head),
          cm_local_call_listed), direct_call);
      term local_tail_term =
          `cm_local_codegen_ok (p:cm_program)
             (target:int->int) (a1:(tvm_inst)list)
             ${annotation_tail:(int)list}`;
      thm local_tail =
          cm_pick_conjunct(local_parts, local_tail_term);
      term ih_term =
          `!(p:cm_program) (target:int->int) (obj:tvm_object)
             (heights:(int)list) pc annotations.
             cm_local_codegen_ok p target
               (a1:(tvm_inst)list) (annotations:(int)list) ==>
             cm_stack_call_insts_from obj heights
               (cm_codegen_function_entries p)
               (cm_codegen_function_arities p) pc
               a1 annotations`;
      thm ih = cm_matching_assumption(branch, ih_term);
      thm tail_calls = mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `target:int->int`, `obj:tvm_object`,
          `heights:(int)list`, `(pc:int) + 1i`,
          annotation_tail), ih), local_tail);
      thm result = conj_rule(listed_call, tail_calls);
      gnode reduced = CONV_TAC(branch,
          reduce_rewrite_conv(THM_LIST(
            annotation_shape,
            get_cm_stack_call_insts_from_def(),
            get_theorem_by_name("NOT_CONS_NIL"),
            get_theorem_by_name("HD"),
            get_theorem_by_name("TL"))));
      ACCEPT_TAC(reduced, result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_local_codegen_calls =
    cm_prove_local_codegen_calls();

PROOF static thm cm_prove_codegen_entries_at(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid.
         0i <= fid &&
         fid < ilength (cm_program_functions p) ==>
         inth fid (cm_codegen_function_entries p) ==
         cm_function_pc p fid`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm bounds = assume_rule(
      `0i <= (fid:int) &&
       fid < ilength (cm_program_functions (p:cm_program))`);
  thm at = mp_rule(specl_rule(TERM_LIST(
      `cm_program_functions (p:cm_program)`, `p:cm_program`,
      `0i`, `fid:int`), cm_function_entries_at), bounds);
  thm zero = int_arith_rule(`0i + (fid:int) == fid`);
  thm pc = trans_rule(at, beta_norm(ap_term_rule(
      `\index:int. cm_function_pc (p:cm_program) index`, zero)));
  thm entries = beta_norm(ap_term_rule(
      `\xs:(int)list. inth (fid:int) xs`,
      cm_codegen_function_entries_def));
  ACCEPT_TAC(leaf, trans_rule(entries, pc));
  return gnode_prove(root);
}
PROOF thm cm_codegen_entries_at =
    cm_prove_codegen_entries_at();

PROOF static thm cm_prove_codegen_arities_at(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid.
         0i <= fid &&
         fid < ilength (cm_program_functions p) ==>
         inth fid (cm_codegen_function_arities p) ==
         ilength (cm_function_params
           (inth fid (cm_program_functions p)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm bounds = assume_rule(
      `0i <= (fid:int) &&
       fid < ilength (cm_program_functions (p:cm_program))`);
  thm at = mp_rule(specl_rule(TERM_LIST(
      `cm_program_functions (p:cm_program)`, `fid:int`),
      cm_function_arities_at), bounds);
  thm arities = beta_norm(ap_term_rule(
      `\xs:(int)list. inth (fid:int) xs`,
      cm_codegen_function_arities_def));
  ACCEPT_TAC(leaf, trans_rule(arities, at));
  return gnode_prove(root);
}
PROOF thm cm_codegen_arities_at =
    cm_prove_codegen_arities_at();

PROOF static thm cm_prove_codegen_entries_length(void) {
  thm entries = ap_term_rule(
      `ilength:(int)list->int`,
      cm_codegen_function_entries_def);
  thm middle = specl_rule(TERM_LIST(
      `cm_program_functions (p:cm_program)`, `p:cm_program`,
      `0i`), cm_entries_arities_length);
  thm arities = ap_term_rule(
      `ilength:(int)list->int`,
      cm_codegen_function_arities_def);
  return gen_rule(`p:cm_program`,
      trans_rule(entries, trans_rule(middle, sym_rule(arities))));
}
PROOF thm cm_codegen_entries_length =
    cm_prove_codegen_entries_length();

PROOF static thm cm_prove_codegen_entries_function_length(void) {
  thm entries = trans_rule(
      ap_term_rule(`ilength:(int)list->int`,
        cm_codegen_function_entries_def),
      trans_rule(specl_rule(TERM_LIST(
          `cm_program_functions (p:cm_program)`, `p:cm_program`,
          `0i`), cm_entries_arities_length),
        spec_rule(`cm_program_functions (p:cm_program)`,
          cm_function_arities_length)));
  return gen_rule(`p:cm_program`, entries);
}
PROOF thm cm_codegen_entries_function_length =
    cm_prove_codegen_entries_function_length();

PROOF static thm cm_prove_codegen_call_sites(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_local_codegen_ok p
           (\address:int.
              inth address (cm_codegen_direct_heights p))
           (cm_model_code p) (cm_codegen_direct_heights p) ==>
         cm_stack_call_sites (cm_compile_model p)
           (cm_codegen_direct_heights p)
           (cm_codegen_function_entries p)
           (cm_codegen_function_arities p)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm local = assume_rule(
      `cm_local_codegen_ok (p:cm_program)
         (\address:int.
            inth address (cm_codegen_direct_heights p))
         (cm_model_code p) (cm_codegen_direct_heights p)`);
  gnode opened = CONV_TAC(leaf,
      reduce_rewrite_conv(THM_LIST(
        get_cm_stack_call_sites_def(),
        get_cm_compile_model_def(),
        get_tvm_object_code_def())));
  gnode_list first = CONJ_TAC(opened);
  ACCEPT_TAC(first[0],
      spec_rule(`p:cm_program`, cm_codegen_entries_length));
  gnode_list second = CONJ_TAC(first[1]);
  {
    gnode entry = AUTO_INTROS_TAC(second[0]);
    thm lower = assume_rule(`0i <= (fid:int)`);
    thm upper_entries = assume_rule(
        `(fid:int) <
         ilength (cm_codegen_function_entries (p:cm_program))`);
    thm entries_length = spec_rule(
        `p:cm_program`, cm_codegen_entries_function_length);
    thm upper_functions = mp_rule(int_arith_rule(mk_imp(
        mk_conj(concl(upper_entries), concl(entries_length)),
        `(fid:int) <
         ilength (cm_program_functions (p:cm_program))`)),
        conj_rule(upper_entries, entries_length));
    thm bounds = conj_rule(lower, upper_functions);
    thm listed_entry = mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`),
        cm_codegen_entries_at), bounds);
    thm listed_arity = mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`),
        cm_codegen_arities_at), bounds);
    thm function_height = mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`),
        cm_function_entry_height), bounds);
    thm selected_entry = beta_norm(ap_term_rule(
        `\address:int.
           inth address (cm_codegen_direct_heights (p:cm_program))`,
        listed_entry));
    thm result = trans_rule(selected_entry,
        trans_rule(function_height, sym_rule(listed_arity)));
    ACCEPT_TAC(entry, result);
  }
  {
    thm calls = mp_rule(specl_rule(TERM_LIST(
        `cm_model_code (p:cm_program)`, `p:cm_program`,
        `\address:int.
           inth address (cm_codegen_direct_heights p)`,
        `cm_compile_model (p:cm_program)`,
        `cm_codegen_direct_heights (p:cm_program)`,
        `0i`, `cm_codegen_direct_heights (p:cm_program)`),
        cm_local_codegen_calls), local);
    ACCEPT_TAC(second[1], conv_rule(rewrite_conv(THM_LIST(
        get_cm_compile_model_def())), calls));
  }
  return gnode_prove(root);
}
PROOF thm cm_codegen_call_sites =
    cm_prove_codegen_call_sites();

PROOF static thm cm_prove_height_stream_drop(void) {
  gnode root = gnode_new_with_ccl(
      `!(target:int->int) pc (prefix:(int)list) suffix.
         cm_height_stream target pc (prefix ++ suffix) ==>
         cm_height_stream target (pc + ilength prefix) suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm stream = assume_rule(
      `cm_height_stream (target:int->int) (pc:int)
         ((prefix:(int)list) ++ (suffix:(int)list))`);
  thm stream_points = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_height_stream_def)),
      concl(stream)), stream);
  gnode point = AUTO_INTROS_TAC(CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_height_stream_def))));
  thm lower = assume_rule(`0i <= (i:int)`);
  thm upper = assume_rule(
      `(i:int) < ilength (suffix:(int)list)`);
  thm prefix_nonnegative = ispec_rule(
      `prefix:(int)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm index_lower = mp_rule(int_arith_rule(mk_imp(
      mk_conj(concl(prefix_nonnegative), concl(lower)),
      `0i <= ilength (prefix:(int)list) + (i:int)`)),
      conj_rule(prefix_nonnegative, lower));
  thm append_length = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_APPEND"))),
      `ilength ((prefix:(int)list) ++ (suffix:(int)list))`);
  thm index_upper = mp_rule(int_arith_rule(mk_imp(
      mk_conj(concl(upper), concl(append_length)),
      `ilength (prefix:(int)list) + (i:int) <
       ilength (prefix ++ suffix)`)),
      conj_rule(upper, append_length));
  thm at = mp_rule(mp_rule(spec_rule(
      `ilength (prefix:(int)list) + (i:int)`,
      stream_points), index_lower), index_upper);
  thm suffix_at = mp_rule(ispecl_rule(TERM_LIST(
      `prefix:(int)list`, `suffix:(int)list`, `i:int`),
      cm_inth_append_right), lower);
  thm address = int_arith_rule(
      `(pc:int) + (ilength (prefix:(int)list) + (i:int)) ==
       (pc + ilength prefix) + i`);
  thm selected_address = beta_norm(ap_term_rule(
      `\address:int. (target:int->int) address`, address));
  thm result = trans_rule(sym_rule(selected_address),
      trans_rule(at, suffix_at));
  ACCEPT_TAC(point, result);
  return gnode_prove(root);
}
PROOF thm cm_height_stream_drop =
    cm_prove_height_stream_drop();

PROOF static thm cm_prove_local_codegen_cons(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (target:int->int) (inst:tvm_inst)
         height (rest:(tvm_inst)list) (annotations:(int)list).
         0i <= height ==>
         cm_local_head_ok target inst height annotations ==>
         (tvm_inst_op inst == TVMCallOp ==>
          ?fid.
            0i <= fid &&
            fid < ilength (cm_program_functions p) &&
            tvm_inst_imm inst == cm_function_pc p fid &&
            height ==
              ilength (cm_function_params
                (inth fid (cm_program_functions p)))) ==>
         cm_local_codegen_ok p target rest annotations ==>
         cm_local_codegen_ok p target
           (inst :: rest) (height :: annotations)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm nonnegative = assume_rule(`0i <= (height:int)`);
  thm head = assume_rule(
      `cm_local_head_ok (target:int->int) (inst:tvm_inst)
         (height:int) (annotations:(int)list)`);
  thm call = assume_rule(
      `tvm_inst_op (inst:tvm_inst) == TVMCallOp ==>
       ?fid.
         0i <= fid &&
         fid < ilength (cm_program_functions (p:cm_program)) &&
         tvm_inst_imm inst == cm_function_pc p fid &&
         (height:int) ==
           ilength (cm_function_params
             (inth fid (cm_program_functions p)))`);
  thm tail = assume_rule(
      `cm_local_codegen_ok (p:cm_program) (target:int->int)
         (rest:(tvm_inst)list) (annotations:(int)list)`);
  CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
      cm_local_codegen_ok_def,
      get_theorem_by_name("NOT_CONS_NIL"),
      get_theorem_by_name("HD"),
      get_theorem_by_name("TL"),
      nonnegative, head, call, tail));
  return gnode_prove(root);
}
PROOF thm cm_local_codegen_cons =
    cm_prove_local_codegen_cons();

PROOF static thm cm_binary_call_contradiction(
    const gnode branch) {
  term call_term =
      `cm_binary_opcode (op:int) == TVMCallOp`;
  thm call = cm_matching_assumption(branch, call_term);
  thm unfolded = conv_rule(
      rewrite_conv(THM_LIST(get_cm_binary_opcode_def())), call);
  thm_list rules = THM_LIST(
      get_datatype_distinctness("tvm_opcode"));
  labeled_term_list assumptions = goal_lasmps(branch->g);
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    if (alpha_compare(assumptions[i].tm, call_term) == 0) {
      continue;
    }
    thm fact = assume_rule(assumptions[i].tm);
    vector_add(&rules, is_not(assumptions[i].tm)
        ? eqf_intro_rule(fact) : eqt_intro_rule(fact));
  }
  return conv_rule(reduce_rewrite_conv(rules), unfolded);
}

PROOF static thm cm_prove_binary_opcode_noncall(void) {
  gnode root = gnode_new_with_ccl(
      `!(op:int). ~(cm_binary_opcode op == TVMCallOp)`);
  gnode frontier = AUTO_INTROS_TAC(root);
  term tags[10] = {
      `2i`, `3i`, `4i`, `5i`, `6i`,
      `7i`, `8i`, `9i`, `10i`, `11i`
  };
  for (size_t i = 0; i < 10; ++i) {
    gnode_list cases = BOOL_CASES_TAC(
        frontier, mk_eq(`op:int`, tags[i]),
        gc_sprintf("hop%zu", i));
    CONTR_TAC(cases[0],
        cm_binary_call_contradiction(cases[0]));
    frontier = cases[1];
  }
  CONTR_TAC(frontier,
      cm_binary_call_contradiction(frontier));
  return gnode_prove(root);
}
PROOF thm cm_binary_opcode_noncall =
    cm_prove_binary_opcode_noncall();

PROOF static thm cm_prove_binary_opcode_head(void) {
  gnode root = gnode_new_with_ccl(
      `!(op:int) (target:int->int) height annotations.
         cm_local_head_ok target
           (TVMInst (cm_binary_opcode op) 0i) height
           (annotations:(int)list) <=>
         (2i <= height &&
          cm_local_next annotations (height - 1i))`);
  gnode frontier = AUTO_INTROS_TAC(root);
  term tags[10] = {
      `2i`, `3i`, `4i`, `5i`, `6i`,
      `7i`, `8i`, `9i`, `10i`, `11i`
  };
  for (size_t i = 0; i < 10; ++i) {
    gnode_list cases = BOOL_CASES_TAC(
        frontier, mk_eq(`op:int`, tags[i]),
        gc_sprintf("hop%zu", i));
    gnode reduced = CONV_WITH_ASMP_TAC(
        cases[0], reduce_rewrite_conv, THM_LIST(
          get_cm_binary_opcode_def(),
          cm_local_head_ok_def,
          get_tvm_inst_op_def(), get_tvm_inst_imm_def(),
          get_datatype_distinctness("tvm_opcode")));
    if (IS_NULL(reduced->solved)) {
      if (is_false(goal_ccl(reduced->g))) {
        ACCEPT_TAC(reduced,
            cm_matching_assumption(reduced, mk_false()));
      } else {
        ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
      }
    }
    frontier = cases[1];
  }
  gnode final = CONV_WITH_ASMP_TAC(
      frontier, reduce_rewrite_conv, THM_LIST(
        get_cm_binary_opcode_def(),
        cm_local_head_ok_def,
        get_tvm_inst_op_def(), get_tvm_inst_imm_def(),
        get_datatype_distinctness("tvm_opcode")));
  if (IS_NULL(final->solved)) {
    if (is_false(goal_ccl(final->g))) {
      ACCEPT_TAC(final,
          cm_matching_assumption(final, mk_false()));
    } else {
      ACCEPT_TAC(final, taut_rule(goal_ccl(final->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_binary_opcode_head =
    cm_prove_binary_opcode_head();

PROOF static thm cm_local_head_by_arith(
    const term target, const term inst, const term height,
    const term annotations, const thm_list facts) {
  thm_list head_rules = THM_LIST(
      cm_binary_opcode_head, cm_local_head_ok_def,
      get_tvm_inst_op_def(), get_tvm_inst_imm_def(),
      get_datatype_distinctness("tvm_opcode"));
  thm_list effect_rules = THM_LIST();
  for (size_t i = 0; i < vector_size(facts); ++i) {
    vector_add(&effect_rules, eqt_intro_rule(facts[i]));
  }
  thm_list effect_definitions = THM_LIST(
      cm_local_next_def,
      get_theorem_by_name("NOT_CONS_NIL"),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"));
  for (size_t i = 0; i < vector_size(effect_definitions); ++i) {
    vector_add(&effect_rules, effect_definitions[i]);
  }
  return by_defs_arith2(
      `cm_local_head_ok ${target:int->int} ${inst:tvm_inst}
         ${height:int} ${annotations:(int)list}`,
      head_rules, effect_rules, facts);
}

PROOF static thm cm_local_noncall(
    const term p, const term inst, const term height) {
  return by_rewrite(
      `tvm_inst_op ${inst:tvm_inst} == TVMCallOp ==>
       ?fid.
         0i <= fid &&
         fid < ilength (cm_program_functions ${p:cm_program}) &&
         tvm_inst_imm ${inst:tvm_inst} ==
           cm_function_pc ${p:cm_program} fid &&
         ${height:int} ==
           ilength (cm_function_params
             (inth fid (cm_program_functions ${p:cm_program})))`,
      THM_LIST(cm_binary_opcode_noncall,
        get_tvm_inst_op_def(),
        get_datatype_distinctness("tvm_opcode")));
}

PROOF static thm cm_local_prepend(
    const term p, const term target, const term inst,
    const term height, const term rest,
    const term annotations, const thm tail,
    const thm call, const thm_list facts) {
  thm nonnegative = by_defs_arith(
      `0i <= ${height:int}`, THM_LIST(), facts);
  thm head = cm_local_head_by_arith(
      target, inst, height, annotations, facts);
  thm constructor = specl_rule(TERM_LIST(
      p, target, inst, height, rest, annotations),
      cm_local_codegen_cons);
  return mp_rule(mp_rule(mp_rule(mp_rule(
      constructor, nonnegative), head), call), tail);
}

PROOF static thm cm_prove_inth_zero_cons(void) {
  gnode root = gnode_new_with_ccl(
      `!(head:A) (tail:(A)list).
         inth 0i (head :: tail) == head`);
  CONV_TAC(root, reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("INTH_DEF"),
      get_theorem_by_name("NUM_OF_INT_OF_NUM"),
      get_theorem_by_name("NTH_DEF"))));
  return gnode_prove(root);
}
PROOF thm cm_inth_zero_cons =
    cm_prove_inth_zero_cons();

PROOF static thm cm_prove_height_stream_head(void) {
  gnode root = gnode_new_with_ccl(
      `!(target:int->int) pc height rest.
         cm_height_stream target pc
           ((height:int) :: (rest:(int)list)) ==>
         target pc == height`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm stream = assume_rule(
      `cm_height_stream (target:int->int) (pc:int)
         ((height:int) :: (rest:(int)list))`);
  thm points = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_height_stream_def)),
      concl(stream)), stream);
  thm tail_nonnegative = ispec_rule(
      `rest:(int)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm positive = by_defs_arith(
      `0i < ilength ((height:int) :: (rest:(int)list))`,
      THM_LIST(get_theorem_by_name("ILENGTH_DEF")),
      THM_LIST(tail_nonnegative));
  thm at_zero = mp_rule(mp_rule(
      spec_rule(`0i`, points),
      int_arith_rule(`0i <= 0i`)), positive);
  thm result = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_inth_zero_cons,
      int_arith_rule(`(pc:int) + 0i == pc`))), at_zero);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_height_stream_head =
    cm_prove_height_stream_head();

PROOF static thm cm_prove_stream_local_next(void) {
  gnode root = gnode_new_with_ccl(
      `!(target:int->int) pc annotations height.
         cm_height_stream target pc (annotations:(int)list) ==>
         cm_local_next annotations height ==>
         target pc == height`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases =
      CASES_TAC(leaf, `annotations:(int)list`, "hannotations");
  {
    thm shape = cm_matching_assumption(cases[0],
        `(annotations:(int)list) == ([]:(int)list)`);
    thm next = cm_matching_assumption(cases[0],
        `cm_local_next (annotations:(int)list) (height:int)`);
    thm impossible = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          shape, cm_local_next_def)), next);
    CONTR_TAC(cases[0], impossible);
  }
  {
    labeled_term_list assumptions = goal_lasmps(cases[1]->g);
    thm shape = assume_rule(assumptions[labeled_term_list_index(
        assumptions, "hannotations")].tm);
    dest_comb_results outer = dest_comb(rhs_of(shape));
    dest_comb_results inner = dest_comb(outer.tm1);
    term head = inner.tm2;
    term tail = outer.tm2;
    thm stream = cm_matching_assumption(cases[1],
        `cm_height_stream (target:int->int) (pc:int)
           (annotations:(int)list)`);
    thm next = cm_matching_assumption(cases[1],
        `cm_local_next (annotations:(int)list) (height:int)`);
    thm stream_cons = conv_rule(
        rewrite_conv(THM_LIST(shape)), stream);
    thm target_head = mp_rule(specl_rule(TERM_LIST(
        `target:int->int`, `pc:int`, head, tail),
        cm_height_stream_head), stream_cons);
    thm head_height = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          shape, cm_local_next_def,
          get_theorem_by_name("HD"),
          get_theorem_by_name("TL"),
          get_theorem_by_name("NOT_CONS_NIL"))),
        next);
    ACCEPT_TAC(cases[1],
        trans_rule(target_head, head_height));
  }
  return gnode_prove(root);
}
PROOF thm cm_stream_local_next =
    cm_prove_stream_local_next();

PROOF static thm cm_prove_args_wf_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(args:(cm_expr)list).
         !(p:cm_program) (f:cm_function_d) slots.
         cm_args_wf p f args (slots:(cm_slot_d)list) ==>
         ilength args == ilength slots`);
  gnode_list cases =
      INDUCT_TAC(root, `args:(cm_expr)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm wf = cm_matching_assumption(leaf,
        `cm_args_wf (p:cm_program) (f:cm_function_d)
           ([]:(cm_expr)list) (slots:(cm_slot_d)list)`);
    thm slots_empty = conv_rule(
        rewrite_conv(THM_LIST(get_cm_args_wf_def())), wf);
    ACCEPT_TAC(leaf, by_rewrite(goal_ccl(leaf->g),
        THM_LIST(slots_empty, get_theorem_by_name("ILENGTH_DEF"))));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list slot_cases =
        CASES_TAC(leaf, `slots:(cm_slot_d)list`, "hslots");
    {
      thm wf = cm_matching_assumption(slot_cases[0],
          `cm_args_wf (p:cm_program) (f:cm_function_d)
             ((a0:cm_expr) :: (a1:(cm_expr)list))
             (slots:(cm_slot_d)list)`);
      thm shape = cm_matching_assumption(slot_cases[0],
          `(slots:(cm_slot_d)list) == ([]:(cm_slot_d)list)`);
      thm impossible = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            shape, get_cm_args_wf_def())), wf);
      CONTR_TAC(slot_cases[0], impossible);
    }
    {
      gnode branch = slot_cases[1];
      labeled_term_list assumptions = goal_lasmps(branch->g);
      thm shape = assume_rule(assumptions[
          labeled_term_list_index(assumptions, "hslots")].tm);
      dest_comb_results outer = dest_comb(rhs_of(shape));
      dest_comb_results inner = dest_comb(outer.tm1);
      term slot_tail = outer.tm2;
      thm wf = cm_matching_assumption(branch,
          `cm_args_wf (p:cm_program) (f:cm_function_d)
             ((a0:cm_expr) :: (a1:(cm_expr)list))
             (slots:(cm_slot_d)list)`);
      thm wf_parts = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            shape, get_cm_args_wf_def(),
            get_theorem_by_name("HD"),
            get_theorem_by_name("TL"),
            get_theorem_by_name("NOT_CONS_NIL"))),
          wf);
      thm tail_wf = cm_pick_conjunct(wf_parts,
          `cm_args_wf (p:cm_program) (f:cm_function_d)
             (a1:(cm_expr)list) ${slot_tail:(cm_slot_d)list}`);
      thm ih = cm_matching_assumption(branch,
          `!(p:cm_program) (f:cm_function_d) slots.
             cm_args_wf p f (a1:(cm_expr)list)
               (slots:(cm_slot_d)list) ==>
             ilength a1 == ilength slots`);
      thm tail_length = mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `f:cm_function_d`, slot_tail), ih),
          tail_wf);
      gnode reduced = CONV_TAC(branch,
          reduce_rewrite_conv(THM_LIST(
            shape, get_theorem_by_name("ILENGTH_DEF"))));
      ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
          concl(tail_length), goal_ccl(reduced->g))), tail_length));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_args_wf_length =
    cm_prove_args_wf_length();

PROOF static thm cm_fact_with_conclusion(
    const thm_list facts, const term wanted) {
  for (size_t i = 0; i < vector_size(facts); ++i) {
    if (alpha_compare(concl(facts[i]), wanted) == 0) {
      return facts[i];
    }
  }
  ENSURE_COND(false, "Missing fact `%s`", string_of_term(wanted));
err:
  ERR_FUN_PUTS("cm_fact_with_conclusion",
      cstr_thm_list(facts), cstr_term(wanted));
  return empty_theorem;
}

PROOF thm cm_local_fixed(
    const term p, const term target,
    const term instructions, const term annotations,
    const term tail, const term tail_annotations,
    const thm tail_ok, const thm boundary,
    const thm_list facts) {
  term_list insts = TERM_LIST();
  term_list heights = TERM_LIST();
  term code_cursor = instructions;
  term height_cursor = annotations;
  while (!equals_term(code_cursor, `[]:(tvm_inst)list`)) {
    ENSURE_COND(is_comb(code_cursor),
        "Instruction fragment is not a concrete list");
    dest_comb_results code_outer = dest_comb(code_cursor);
    ENSURE_COND(is_comb(code_outer.tm1),
        "Instruction fragment has no concrete head");
    dest_comb_results code_inner = dest_comb(code_outer.tm1);
    vector_add(&insts, code_inner.tm2);
    code_cursor = code_outer.tm2;
  }
  while (!equals_term(height_cursor, `[]:(int)list`)) {
    ENSURE_COND(is_comb(height_cursor),
        "Height fragment is not a concrete list");
    dest_comb_results height_outer = dest_comb(height_cursor);
    ENSURE_COND(is_comb(height_outer.tm1),
        "Height fragment has no concrete head");
    dest_comb_results height_inner = dest_comb(height_outer.tm1);
    vector_add(&heights, height_inner.tm2);
    height_cursor = height_outer.tm2;
  }
  ENSURE_COND(vector_size(insts) == vector_size(heights),
      "Fixed instruction and height fragments differ in length");
  thm current = tail_ok;
  term current_code = tail;
  term current_heights = tail_annotations;
  thm next = boundary;
  for (size_t i = vector_size(insts); i > 0; --i) {
    term inst = insts[i - 1];
    term height = heights[i - 1];
    dest_comb_results inst_outer = dest_comb(inst);
    dest_comb_results inst_middle = dest_comb(inst_outer.tm1);
    term op = inst_middle.tm2;
    thm_list step_facts = (thm_list)vector_copy(facts);
    if (!IS_NULL(next)) {
      thm next_parts = conv_rule(
          rewrite_conv(THM_LIST(cm_local_next_def)), next);
      vector_add(&step_facts, conjunct1_rule(next_parts));
      vector_add(&step_facts, conjunct2_rule(next_parts));
    }
    thm call;
    if (equals_term(op, `TVMCallOp`)) {
      term wanted =
          `tvm_inst_op ${inst:tvm_inst} == TVMCallOp ==>
           ?fid.
             0i <= fid &&
             fid < ilength
               (cm_program_functions ${p:cm_program}) &&
             tvm_inst_imm ${inst:tvm_inst} ==
               cm_function_pc ${p:cm_program} fid &&
             ${height:int} ==
               ilength (cm_function_params
                 (inth fid
                   (cm_program_functions ${p:cm_program})))`;
      call = cm_fact_with_conclusion(step_facts, wanted);
    } else {
      call = cm_local_noncall(p, inst, height);
    }
    current = cm_local_prepend(
        p, target, inst, height, current_code,
        current_heights, current, call, step_facts);
    current_code =
        `(${inst:tvm_inst}) :: ${current_code:(tvm_inst)list}`;
    current_heights =
        `(${height:int}) :: ${current_heights:(int)list}`;
    next = by_rewrite(
        `cm_local_next ${current_heights:(int)list}
           ${height:int}`,
        THM_LIST(cm_local_next_def,
          get_theorem_by_name("NOT_CONS_NIL"),
          get_theorem_by_name("HD"),
          get_theorem_by_name("TL")));
  }
  return current;
err:
  ERR_FUN_PUTS("cm_local_fixed",
      cstr_term(instructions), cstr_term(annotations));
  return empty_theorem;
}

PROOF static thm cm_prove_local_push_fragment(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (target:int->int) imm height
         (tail:(tvm_inst)list) (annotations:(int)list).
         0i <= height ==>
         cm_local_next annotations (height + 1i) ==>
         cm_local_codegen_ok p target tail annotations ==>
         cm_local_codegen_ok p target
           ((TVMInst TVMPushOp imm) :: tail)
           (height :: annotations)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm lower = assume_rule(`0i <= (height:int)`);
  thm boundary = assume_rule(
      `cm_local_next (annotations:(int)list)
         ((height:int) + 1i)`);
  thm tail = assume_rule(
      `cm_local_codegen_ok (p:cm_program) (target:int->int)
         (tail:(tvm_inst)list) (annotations:(int)list)`);
  thm result = cm_local_fixed(
      `p:cm_program`, `target:int->int`,
      `[(TVMInst TVMPushOp (imm:int))]`,
      `[(height:int)]`, `tail:(tvm_inst)list`,
      `annotations:(int)list`, tail, boundary,
      THM_LIST(lower));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_local_push_fragment =
    cm_prove_local_push_fragment();

PROOF static thm cm_prove_local_fp_address(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (target:int->int) offset height
         (tail:(tvm_inst)list) (annotations:(int)list).
         0i <= height ==>
         cm_local_next annotations (height + 1i) ==>
         cm_local_codegen_ok p target tail annotations ==>
         cm_local_codegen_ok p target
           (cm_fp_relative_address_code offset ++ tail)
           (cm_fp_address_heights height ++ annotations)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm lower = assume_rule(`0i <= (height:int)`);
  thm boundary = assume_rule(
      `cm_local_next (annotations:(int)list)
         ((height:int) + 1i)`);
  thm tail_ok = assume_rule(
      `cm_local_codegen_ok (p:cm_program) (target:int->int)
         (tail:(tvm_inst)list) (annotations:(int)list)`);
  thm result = cm_local_fixed(
      `p:cm_program`, `target:int->int`,
      `[TVMInst TVMPushOp 8i; TVMInst TVMLoadOp 0i;
        TVMInst TVMPushOp (offset:int); TVMInst TVMAddOp 0i]`,
      `[(height:int); height + 1i; height + 1i; height + 2i]`,
      `tail:(tvm_inst)list`, `annotations:(int)list`,
      tail_ok, boundary, THM_LIST(lower));
  gnode reduced = CONV_TAC(leaf,
      reduce_rewrite_conv(THM_LIST(
        get_cm_fp_relative_address_code_def(),
        cm_fp_address_heights_def,
        get_theorem_by_name("APPEND"))));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}
PROOF thm cm_local_fp_address =
    cm_prove_local_fp_address();

PROOF static thm cm_prove_local_temp_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (target:int->int) fid slot height
         (tail:(tvm_inst)list) (annotations:(int)list).
         1i <= height ==>
         cm_local_next annotations (height - 1i) ==>
         cm_local_codegen_ok p target tail annotations ==>
         cm_local_codegen_ok p target
           (cm_temp_store_code p fid slot ++ tail)
           (cm_temp_access_heights height ++ annotations)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm lower = assume_rule(`1i <= (height:int)`);
  thm boundary = assume_rule(
      `cm_local_next (annotations:(int)list)
         ((height:int) - 1i)`);
  thm tail_ok = assume_rule(
      `cm_local_codegen_ok (p:cm_program) (target:int->int)
         (tail:(tvm_inst)list) (annotations:(int)list)`);
  thm result = cm_local_fixed(
      `p:cm_program`, `target:int->int`,
      `[TVMInst TVMPushOp 8i; TVMInst TVMLoadOp 0i;
        TVMInst TVMPushOp (cm_temp_offset p fid slot);
        TVMInst TVMAddOp 0i; TVMInst TVMStoreOp 0i]`,
      `[(height:int); height + 1i; height + 1i;
        height + 2i; height + 1i]`,
      `tail:(tvm_inst)list`, `annotations:(int)list`,
      tail_ok, boundary, THM_LIST(lower));
  gnode reduced = CONV_TAC(leaf,
      reduce_rewrite_conv(THM_LIST(
        get_cm_temp_store_code_def(),
        get_cm_fp_relative_address_code_def(),
        cm_temp_access_heights_def,
        get_theorem_by_name("APPEND"))));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}
PROOF thm cm_local_temp_store =
    cm_prove_local_temp_store();

PROOF static thm cm_prove_local_temp_load(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (target:int->int) fid slot height
         (tail:(tvm_inst)list) (annotations:(int)list).
         0i <= height ==>
         cm_local_next annotations (height + 1i) ==>
         cm_local_codegen_ok p target tail annotations ==>
         cm_local_codegen_ok p target
           (cm_temp_load_code p fid slot ++ tail)
           (cm_temp_access_heights height ++ annotations)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm lower = assume_rule(`0i <= (height:int)`);
  thm boundary = assume_rule(
      `cm_local_next (annotations:(int)list)
         ((height:int) + 1i)`);
  thm tail_ok = assume_rule(
      `cm_local_codegen_ok (p:cm_program) (target:int->int)
         (tail:(tvm_inst)list) (annotations:(int)list)`);
  thm result = cm_local_fixed(
      `p:cm_program`, `target:int->int`,
      `[TVMInst TVMPushOp 8i; TVMInst TVMLoadOp 0i;
        TVMInst TVMPushOp (cm_temp_offset p fid slot);
        TVMInst TVMAddOp 0i; TVMInst TVMLoadOp 0i]`,
      `[(height:int); height + 1i; height + 1i;
        height + 2i; height + 1i]`,
      `tail:(tvm_inst)list`, `annotations:(int)list`,
      tail_ok, boundary, THM_LIST(lower));
  gnode reduced = CONV_TAC(leaf,
      reduce_rewrite_conv(THM_LIST(
        get_cm_temp_load_code_def(),
        get_cm_fp_relative_address_code_def(),
        cm_temp_access_heights_def,
        get_theorem_by_name("APPEND"))));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}
PROOF thm cm_local_temp_load =
    cm_prove_local_temp_load();

PROOF static thm cm_prove_local_char_normalize(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (target:int->int) ty height
         (tail:(tvm_inst)list) (annotations:(int)list).
         1i <= height ==>
         cm_local_next annotations height ==>
         cm_local_codegen_ok p target tail annotations ==>
         cm_local_codegen_ok p target
           (cm_char_normalize_code ty ++ tail)
           (cm_normalize_heights ty height ++ annotations)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm lower = assume_rule(`1i <= (height:int)`);
  thm boundary = assume_rule(
      `cm_local_next (annotations:(int)list) (height:int)`);
  thm tail_ok = assume_rule(
      `cm_local_codegen_ok (p:cm_program) (target:int->int)
         (tail:(tvm_inst)list) (annotations:(int)list)`);
  gnode_list cases =
      BOOL_CASES_TAC(leaf, `(ty:cm_type) == CMCharTy`, "hchar");
  {
    thm is_char = cm_matching_assumption(
        cases[0], `(ty:cm_type) == CMCharTy`);
    thm result = cm_local_fixed(
        `p:cm_program`, `target:int->int`,
        `[TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
          TVMInst TVMPushOp 256i; TVMInst TVMAddOp 0i;
          TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i]`,
        `[(height:int); height + 1i; height;
          height + 1i; height; height + 1i]`,
        `tail:(tvm_inst)list`, `annotations:(int)list`,
        tail_ok, boundary, THM_LIST(lower));
    gnode reduced = CONV_TAC(cases[0],
        reduce_rewrite_conv(THM_LIST(
          is_char, get_cm_char_normalize_code_def(),
          cm_normalize_heights_def,
          get_theorem_by_name("APPEND"))));
    ACCEPT_TAC(reduced, result);
  }
  {
    thm not_char = cm_matching_assumption(
        cases[1], `~((ty:cm_type) == CMCharTy)`);
    gnode reduced = CONV_TAC(cases[1],
        reduce_rewrite_conv(THM_LIST(
          not_char, get_cm_char_normalize_code_def(),
          cm_normalize_heights_def,
          get_theorem_by_name("APPEND"))));
    ACCEPT_TAC(reduced, tail_ok);
  }
  return gnode_prove(root);
}
PROOF thm cm_local_char_normalize =
    cm_prove_local_char_normalize();

PROOF static thm cm_prove_local_load(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (target:int->int) ty height
         (tail:(tvm_inst)list) (annotations:(int)list).
         1i <= height ==>
         cm_local_next annotations height ==>
         cm_local_codegen_ok p target tail annotations ==>
         cm_local_codegen_ok p target
           (cm_load_code ty ++ tail)
           (height :: annotations)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm lower = assume_rule(`1i <= (height:int)`);
  thm boundary = assume_rule(
      `cm_local_next (annotations:(int)list) (height:int)`);
  thm tail_ok = assume_rule(
      `cm_local_codegen_ok (p:cm_program) (target:int->int)
         (tail:(tvm_inst)list) (annotations:(int)list)`);
  gnode_list cases =
      BOOL_CASES_TAC(leaf, `(ty:cm_type) == CMCharTy`, "hchar");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm condition = assume_rule(
        goal_lasmps(cases[i]->g)[labeled_term_list_index(
          goal_lasmps(cases[i]->g), "hchar")].tm);
    term op = i == 0 ? `TVMLoadBOp` : `TVMLoadOp`;
    thm result = cm_local_fixed(
        `p:cm_program`, `target:int->int`,
        `[TVMInst ${op:tvm_opcode} 0i]`,
        `[(height:int)]`, `tail:(tvm_inst)list`,
        `annotations:(int)list`, tail_ok, boundary,
        THM_LIST(lower));
    gnode reduced = CONV_TAC(cases[i],
        reduce_rewrite_conv(THM_LIST(
          condition, get_cm_load_code_def(),
          get_theorem_by_name("APPEND"))));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_local_load =
    cm_prove_local_load();

PROOF static thm cm_prove_local_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (target:int->int) ty height
         (tail:(tvm_inst)list) (annotations:(int)list).
         2i <= height ==>
         cm_local_next annotations (height - 2i) ==>
         cm_local_codegen_ok p target tail annotations ==>
         cm_local_codegen_ok p target
           (cm_store_code ty ++ tail)
           (height :: annotations)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm lower = assume_rule(`2i <= (height:int)`);
  thm boundary = assume_rule(
      `cm_local_next (annotations:(int)list)
         ((height:int) - 2i)`);
  thm tail_ok = assume_rule(
      `cm_local_codegen_ok (p:cm_program) (target:int->int)
         (tail:(tvm_inst)list) (annotations:(int)list)`);
  gnode_list cases =
      BOOL_CASES_TAC(leaf, `(ty:cm_type) == CMCharTy`, "hchar");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm condition = assume_rule(
        goal_lasmps(cases[i]->g)[labeled_term_list_index(
          goal_lasmps(cases[i]->g), "hchar")].tm);
    term op = i == 0 ? `TVMStoreBOp` : `TVMStoreOp`;
    thm result = cm_local_fixed(
        `p:cm_program`, `target:int->int`,
        `[TVMInst ${op:tvm_opcode} 0i]`,
        `[(height:int)]`, `tail:(tvm_inst)list`,
        `annotations:(int)list`, tail_ok, boundary,
        THM_LIST(lower));
    gnode reduced = CONV_TAC(cases[i],
        reduce_rewrite_conv(THM_LIST(
          condition, get_cm_store_code_def(),
          get_theorem_by_name("APPEND"))));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_local_store =
    cm_prove_local_store();

PROOF static thm cm_prove_local_binding_address(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (target:int->int) fid scope slot
         (tail:(tvm_inst)list) (annotations:(int)list).
         cm_local_next annotations 1i ==>
         cm_local_codegen_ok p target tail annotations ==>
         cm_local_codegen_ok p target
           (cm_binding_address_code p fid scope slot ++ tail)
           (cm_binding_address_heights scope ++ annotations)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm boundary = assume_rule(
      `cm_local_next (annotations:(int)list) 1i`);
  thm tail_ok = assume_rule(
      `cm_local_codegen_ok (p:cm_program) (target:int->int)
         (tail:(tvm_inst)list) (annotations:(int)list)`);
  gnode_list cases =
      BOOL_CASES_TAC(leaf, `(scope:int) == 0i`, "hglobal");
  {
    thm global = cm_matching_assumption(
        cases[0], `(scope:int) == 0i`);
    thm result = cm_local_fixed(
        `p:cm_program`, `target:int->int`,
        `[TVMInst TVMPushOp (cm_global_address p slot)]`,
        `[0i]`, `tail:(tvm_inst)list`,
        `annotations:(int)list`, tail_ok, boundary,
        THM_LIST());
    gnode reduced = CONV_TAC(cases[0],
        reduce_rewrite_conv(THM_LIST(
          global, get_cm_binding_address_code_def(),
          get_cm_push_code_def(),
          cm_binding_address_heights_def,
          get_theorem_by_name("APPEND"))));
    ACCEPT_TAC(reduced, result);
  }
  {
    thm nonglobal = cm_matching_assumption(
        cases[1], `~((scope:int) == 0i)`);
    thm result = cm_local_fixed(
        `p:cm_program`, `target:int->int`,
        `[TVMInst TVMPushOp 8i; TVMInst TVMLoadOp 0i;
          TVMInst TVMPushOp
            (if scope == 1i
             then cm_local_offset p fid slot
             else cm_param_offset p fid slot);
          TVMInst TVMAddOp 0i]`,
        `[0i; 1i; 1i; 2i]`,
        `tail:(tvm_inst)list`, `annotations:(int)list`,
        tail_ok, boundary, THM_LIST());
    gnode reduced = CONV_TAC(cases[1],
        reduce_rewrite_conv(THM_LIST(
          nonglobal, get_cm_binding_address_code_def(),
          get_cm_fp_relative_address_code_def(),
          cm_binding_address_heights_def,
          get_theorem_by_name("APPEND"))));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_local_binding_address =
    cm_prove_local_binding_address();

PROOF static thm cm_prove_local_return_epilogue(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (target:int->int)
         (tail:(tvm_inst)list) (annotations:(int)list).
         cm_local_codegen_ok p target tail annotations ==>
         cm_local_codegen_ok p target
           (cm_return_epilogue ++ tail)
           (cm_return_heights ++ annotations)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm tail_ok = assume_rule(
      `cm_local_codegen_ok (p:cm_program) (target:int->int)
         (tail:(tvm_inst)list) (annotations:(int)list)`);
  thm result = cm_local_fixed(
      `p:cm_program`, `target:int->int`,
      `[TVMInst TVMPushOp 8i; TVMInst TVMLoadOp 0i;
        TVMInst TVMLoadOp 0i; TVMInst TVMPushOp 8i;
        TVMInst TVMStoreOp 0i; TVMInst TVMRetOp 0i]`,
      `[1i; 2i; 2i; 2i; 3i; 1i]`,
      `tail:(tvm_inst)list`, `annotations:(int)list`,
      tail_ok, empty_theorem, THM_LIST());
  gnode reduced = CONV_TAC(leaf,
      reduce_rewrite_conv(THM_LIST(
        get_cm_return_epilogue_def(),
        cm_return_heights_def,
        get_theorem_by_name("APPEND"))));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}
PROOF thm cm_local_return_epilogue =
    cm_prove_local_return_epilogue();

PROOF static void cm_accept_binary_finish(
    const gnode branch, const thm result,
    const thm_list conditions) {
  thm_list rules = THM_LIST();
  for (size_t i = 0; i < vector_size(conditions); ++i) {
    vector_add(&rules, is_not(concl(conditions[i]))
        ? eqf_intro_rule(conditions[i])
        : eqt_intro_rule(conditions[i]));
  }
  thm_list definitions = THM_LIST(
      get_cm_binary_finish_code_def(),
      get_cm_temp_load_code_def(),
      get_cm_fp_relative_address_code_def(),
      cm_binary_finish_heights_def,
      cm_temp_access_heights_def,
      get_theorem_by_name("APPEND"));
  for (size_t i = 0; i < vector_size(definitions); ++i) {
    vector_add(&rules, definitions[i]);
  }
  gnode reduced = CONV_TAC(
      branch, reduce_rewrite_conv(rules));
  ACCEPT_TAC(reduced, result);
}

PROOF static thm cm_prove_local_binary_finish(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (target:int->int) fid op left right temp
         (tail:(tvm_inst)list) (annotations:(int)list).
         cm_local_next annotations 1i ==>
         cm_local_codegen_ok p target tail annotations ==>
         cm_local_codegen_ok p target
           (cm_binary_finish_code p fid op left right temp ++ tail)
           (cm_binary_finish_heights p op left right ++ annotations)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm boundary = assume_rule(
      `cm_local_next (annotations:(int)list) 1i`);
  thm tail_ok = assume_rule(
      `cm_local_codegen_ok (p:cm_program) (target:int->int)
         (tail:(tvm_inst)list) (annotations:(int)list)`);
  term conditions[4] = {
      `(op:int) == 8i &&
       cm_is_pointer (cm_expr_type (right:cm_expr))`,
      `(op:int) == 8i &&
       cm_is_pointer (cm_expr_type (left:cm_expr))`,
      `(op:int) == 9i &&
       cm_is_pointer (cm_expr_type (left:cm_expr)) &&
       cm_is_pointer (cm_expr_type (right:cm_expr))`,
      `(op:int) == 9i &&
       cm_is_pointer (cm_expr_type (left:cm_expr))`
  };
  thm_list negatives = THM_LIST();
  gnode frontier = leaf;
  for (size_t i = 0; i < 4; ++i) {
    gnode_list cases = BOOL_CASES_TAC(
        frontier, conditions[i], gc_sprintf("hfinish%zu", i));
    thm positive = cm_matching_assumption(cases[0], conditions[i]);
    thm_list branch_conditions =
        (thm_list)vector_copy(negatives);
    vector_add(&branch_conditions, positive);
    term instructions;
    term heights;
    if (i == 0) {
      instructions =
          `[TVMInst TVMPushOp 8i; TVMInst TVMLoadOp 0i;
            TVMInst TVMPushOp (cm_temp_offset p fid temp);
            TVMInst TVMAddOp 0i; TVMInst TVMLoadOp 0i;
            TVMInst TVMPushOp (cm_pointer_scale p right);
            TVMInst TVMMulOp 0i; TVMInst TVMSwapOp 0i;
            TVMInst TVMAddOp 0i]`;
      heights = `[1i; 2i; 2i; 3i; 2i; 2i; 3i; 2i; 2i]`;
    } else if (i == 1) {
      instructions =
          `[TVMInst TVMPushOp 8i; TVMInst TVMLoadOp 0i;
            TVMInst TVMPushOp (cm_temp_offset p fid temp);
            TVMInst TVMAddOp 0i; TVMInst TVMLoadOp 0i;
            TVMInst TVMSwapOp 0i;
            TVMInst TVMPushOp (cm_pointer_scale p left);
            TVMInst TVMMulOp 0i; TVMInst TVMAddOp 0i]`;
      heights = `[1i; 2i; 2i; 3i; 2i; 2i; 2i; 3i; 2i]`;
    } else if (i == 2) {
      instructions =
          `[TVMInst TVMPushOp 8i; TVMInst TVMLoadOp 0i;
            TVMInst TVMPushOp (cm_temp_offset p fid temp);
            TVMInst TVMAddOp 0i; TVMInst TVMLoadOp 0i;
            TVMInst TVMSwapOp 0i; TVMInst TVMSubOp 0i;
            TVMInst TVMPushOp (cm_pointer_scale p left);
            TVMInst TVMDivOp 0i]`;
      heights = `[1i; 2i; 2i; 3i; 2i; 2i; 2i; 1i; 2i]`;
    } else {
      instructions =
          `[TVMInst TVMPushOp 8i; TVMInst TVMLoadOp 0i;
            TVMInst TVMPushOp (cm_temp_offset p fid temp);
            TVMInst TVMAddOp 0i; TVMInst TVMLoadOp 0i;
            TVMInst TVMSwapOp 0i;
            TVMInst TVMPushOp (cm_pointer_scale p left);
            TVMInst TVMMulOp 0i; TVMInst TVMSubOp 0i]`;
      heights = `[1i; 2i; 2i; 3i; 2i; 2i; 2i; 3i; 2i]`;
    }
    thm result = cm_local_fixed(
        `p:cm_program`, `target:int->int`,
        instructions, heights,
        `tail:(tvm_inst)list`, `annotations:(int)list`,
        tail_ok, boundary, THM_LIST());
    cm_accept_binary_finish(
        cases[0], result, branch_conditions);
    thm negative = cm_matching_assumption(
        cases[1], mk_not(conditions[i]));
    vector_add(&negatives, negative);
    frontier = cases[1];
  }
  {
    thm result = cm_local_fixed(
        `p:cm_program`, `target:int->int`,
        `[TVMInst TVMPushOp 8i; TVMInst TVMLoadOp 0i;
          TVMInst TVMPushOp (cm_temp_offset p fid temp);
          TVMInst TVMAddOp 0i; TVMInst TVMLoadOp 0i;
          TVMInst TVMSwapOp 0i;
          TVMInst (cm_binary_opcode op) 0i]`,
        `[1i; 2i; 2i; 3i; 2i; 2i; 2i]`,
        `tail:(tvm_inst)list`, `annotations:(int)list`,
        tail_ok, boundary, THM_LIST());
    cm_accept_binary_finish(frontier, result, negatives);
  }
  return gnode_prove(root);
}
PROOF thm cm_local_binary_finish =
    cm_prove_local_binary_finish();

PROOF static thm cm_prove_args_reload_starts(void) {
  gnode root = gnode_new_with_ccl(
      `!(args:(cm_expr)list).
         !height (annotations:(int)list).
         cm_local_next annotations
           (height + ilength args) ==>
         cm_local_next
           (cm_args_reload_heights height args ++ annotations)
           height`);
  gnode_list cases =
      INDUCT_TAC(root, `args:(cm_expr)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm boundary = cm_matching_assumption(leaf,
        `cm_local_next (annotations:(int)list)
           ((height:int) + ilength ([]:(cm_expr)list))`);
    thm length_nil = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ([]:(cm_expr)list)`);
    thm index = mp_rule(int_arith_rule(mk_imp(
        concl(length_nil),
        `(height:int) + ilength ([]:(cm_expr)list) ==
         height`)), length_nil);
    thm transported = eq_mp_rule(beta_norm(ap_term_rule(
        `\next_height:int.
           cm_local_next (annotations:(int)list) next_height`,
        index)), boundary);
    gnode reduced = CONV_TAC(leaf,
        reduce_rewrite_conv(THM_LIST(
          cm_args_reload_heights_def,
          get_theorem_by_name("APPEND"))));
    ACCEPT_TAC(reduced, transported);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    ACCEPT_TAC(leaf, by_rewrite(goal_ccl(leaf->g), THM_LIST(
        cm_args_reload_heights_def,
        cm_temp_access_heights_def,
        cm_local_next_def,
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("NOT_CONS_NIL"),
        get_theorem_by_name("HD"),
        get_theorem_by_name("TL"))));
  }
  return gnode_prove(root);
}
PROOF thm cm_args_reload_starts =
    cm_prove_args_reload_starts();

PROOF static thm cm_prove_local_args_reload(void) {
  gnode root = gnode_new_with_ccl(
      `!(args:(cm_expr)list).
         !(p:cm_program) (target:int->int) fid slot height
           (tail:(tvm_inst)list) (annotations:(int)list).
         0i <= height ==>
         cm_local_next annotations
           (height + ilength args) ==>
         cm_local_codegen_ok p target tail annotations ==>
         cm_local_codegen_ok p target
           (cm_emit_args_reload p fid slot args ++ tail)
           (cm_args_reload_heights height args ++ annotations)`);
  gnode_list cases =
      INDUCT_TAC(root, `args:(cm_expr)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm tail_ok = cm_matching_assumption(leaf,
        `cm_local_codegen_ok (p:cm_program) (target:int->int)
           (tail:(tvm_inst)list) (annotations:(int)list)`);
    gnode reduced = CONV_TAC(leaf,
        reduce_rewrite_conv(THM_LIST(
          get_cm_emit_args_reload_def(),
          cm_args_reload_heights_def,
          get_theorem_by_name("APPEND"))));
    ACCEPT_TAC(reduced, tail_ok);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm lower = cm_matching_assumption(
        leaf, `0i <= (height:int)`);
    thm boundary = cm_matching_assumption(leaf,
        `cm_local_next (annotations:(int)list)
           ((height:int) +
             ilength ((a0:cm_expr) :: (a1:(cm_expr)list)))`);
    thm tail_ok = cm_matching_assumption(leaf,
        `cm_local_codegen_ok (p:cm_program) (target:int->int)
           (tail:(tvm_inst)list) (annotations:(int)list)`);
    thm ih = cm_matching_assumption(leaf,
        `!(p:cm_program) (target:int->int) fid slot height
           (tail:(tvm_inst)list) (annotations:(int)list).
           0i <= height ==>
           cm_local_next annotations
             (height + ilength (a1:(cm_expr)list)) ==>
           cm_local_codegen_ok p target tail annotations ==>
           cm_local_codegen_ok p target
             (cm_emit_args_reload p fid slot a1 ++ tail)
             (cm_args_reload_heights height a1 ++ annotations)`);
    thm next_lower = mp_rule(int_arith_rule(mk_imp(
        concl(lower), `0i <= (height:int) + 1i`)), lower);
    thm length_cons = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ((a0:cm_expr) :: (a1:(cm_expr)list))`);
    thm boundary_index = mp_rule(int_arith_rule(mk_imp(
        concl(length_cons),
        `(height:int) +
           ilength ((a0:cm_expr) :: (a1:(cm_expr)list)) ==
         (height + 1i) + ilength a1`)), length_cons);
    thm boundary_transport = beta_norm(ap_term_rule(
        `\next_height:int.
           cm_local_next (annotations:(int)list) next_height`,
        boundary_index));
    thm tail_boundary =
        eq_mp_rule(boundary_transport, boundary);
    thm recursive = mp_rule(mp_rule(mp_rule(specl_rule(
        TERM_LIST(`p:cm_program`, `target:int->int`,
          `fid:int`, `(slot:int) + 1i`,
          `(height:int) + 1i`, `tail:(tvm_inst)list`,
          `annotations:(int)list`), ih),
        next_lower), tail_boundary), tail_ok);
    thm recursive_start = mp_rule(specl_rule(TERM_LIST(
        `a1:(cm_expr)list`, `(height:int) + 1i`,
        `annotations:(int)list`),
        cm_args_reload_starts), tail_boundary);
    thm result = mp_rule(mp_rule(mp_rule(specl_rule(
        TERM_LIST(`p:cm_program`, `target:int->int`,
          `fid:int`, `slot:int`, `height:int`,
          `cm_emit_args_reload p fid (slot + 1i)
             (a1:(cm_expr)list) ++ (tail:(tvm_inst)list)`,
          `cm_args_reload_heights (height + 1i)
             (a1:(cm_expr)list) ++ (annotations:(int)list)`),
        cm_local_temp_load), lower), recursive_start), recursive);
    gnode reduced = CONV_TAC(leaf,
        reduce_rewrite_conv(THM_LIST(
          get_cm_emit_args_reload_def(),
          cm_args_reload_heights_def,
          get_theorem_by_name("APPEND_ASSOC"))));
    ACCEPT_TAC(reduced, conv_rule(
        rewrite_conv(THM_LIST(
          get_theorem_by_name("APPEND_ASSOC"))), result));
  }
  return gnode_prove(root);
}
PROOF thm cm_local_args_reload =
    cm_prove_local_args_reload();

PROOF bool cm_term_head_named(
    const term tm, const char *name) {
  term cursor = tm;
  while (is_comb(cursor)) {
    cursor = dest_comb(cursor).tm1;
  }
  return is_const(cursor) &&
      strcmp(dest_const(cursor).s, name) == 0;
}

PROOF thm cm_predicate_assumption(
    const gnode branch, const char *name) {
  labeled_term_list assumptions = goal_lasmps(branch->g);
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    if (cm_term_head_named(assumptions[i].tm, name)) {
      return assume_rule(assumptions[i].tm);
    }
  }
  ENSURE_COND(false, "Missing `%s` assumption", name);
err:
  ERR_FUN_PUTS("cm_predicate_assumption",
      cstr_gnode(branch), cstr_string(name));
  return empty_theorem;
}
PROOF thm cm_expr_start_ih(
    const gnode branch, const term expr, bool lvalue,
    const term suffix, const thm boundary) {
  term ih_term;
  if (lvalue) {
    ih_term =
        `!(p:cm_program) (f:cm_function_d) fid
            (annotations:(int)list).
           cm_expr_wf p f ${expr:cm_expr} ==>
           cm_lvalue ${expr:cm_expr} ==>
           cm_local_next annotations 1i ==>
           cm_local_next
             (cm_lvalue_heights p fid ${expr:cm_expr} ++
              annotations) 0i`;
  } else {
    ih_term =
        `!(p:cm_program) (f:cm_function_d) fid
            (annotations:(int)list).
           cm_expr_wf p f ${expr:cm_expr} ==>
           cm_local_next annotations 1i ==>
           cm_local_next
             (cm_rvalue_heights p fid ${expr:cm_expr} ++
              annotations) 0i`;
  }
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `f:cm_function_d`, `fid:int`, suffix),
      cm_matching_assumption(branch, ih_term));
  result = mp_rule(result, cm_matching_assumption(branch,
      `cm_expr_wf (p:cm_program) (f:cm_function_d)
         ${expr:cm_expr}`));
  if (lvalue) {
    result = mp_rule(result, cm_matching_assumption(branch,
        `cm_lvalue ${expr:cm_expr}`));
  }
  result = mp_rule(result, boundary);
  return conv_rule(rewrite_conv(THM_LIST(
      cm_lvalue_heights_def, cm_rvalue_heights_def)), result);
}
PROOF thm cm_args_start_ih(
    const gnode branch, const term args, const term slots,
    const term suffix, const thm boundary) {
  term ih_term =
      `!(p:cm_program) (f:cm_function_d)
          (slots:(cm_slot_d)list) fid
          (annotations:(int)list).
         cm_args_wf p f ${args:(cm_expr)list} slots ==>
         cm_local_next annotations 0i ==>
         cm_local_next
           (cm_args_store_heights p fid
              ${args:(cm_expr)list} ++ annotations) 0i`;
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `f:cm_function_d`, slots,
      `fid:int`, suffix),
      cm_matching_assumption(branch, ih_term));
  result = mp_rule(result, cm_matching_assumption(branch,
      `cm_args_wf (p:cm_program) (f:cm_function_d)
         ${args:(cm_expr)list} ${slots:(cm_slot_d)list}`));
  return mp_rule(result, boundary);
}


PROOF thm cm_fixed_local_next(
    const term annotations, const term height,
    const thm_list extra_rules) {
  thm_list rules = THM_LIST(
      cm_fp_address_heights_def,
      cm_temp_access_heights_def,
      cm_normalize_heights_def,
      cm_binding_address_heights_def,
      cm_binary_finish_heights_def,
      cm_args_reload_heights_def,
      cm_local_next_def,
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("NOT_CONS_NIL"),
      get_theorem_by_name("HD"),
      get_theorem_by_name("TL"));
  for (size_t i = 0; i < vector_size(extra_rules); ++i) {
    vector_add(&rules, extra_rules[i]);
  }
  return by_rewrite(
      `cm_local_next ${annotations:(int)list} ${height:int}`,
      rules);
}
