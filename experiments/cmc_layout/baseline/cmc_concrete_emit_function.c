#include "cmc_concrete_emit_function.h"
#include "cmc_concrete_emit_stmt_proof.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_emit_stmt.c"
#require "cmc_concrete_emit_return.c"

PROOF static thm cm_prove_slots_prefix_zero(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list).
         cm_slots_prefix structs slots 0i == 0i`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs, `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_slots_prefix_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_slots_prefix_def())));
  }
  return gnode_prove(root);
}
PROOF thm cm_slots_prefix_zero = cm_prove_slots_prefix_zero();

PROOF static thm cm_prove_slots_prefix_append(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (prefix:(cm_slot_d)list)
         (suffix:(cm_slot_d)list).
         cm_slots_prefix structs (prefix ++ suffix) (ilength prefix) ==
         cm_slots_size structs prefix`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs, `prefix:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("ILENGTH_DEF"),
        cm_slots_prefix_zero,
        get_cm_slots_prefix_def(), get_cm_slots_size_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm tail_nonnegative = ispec_rule(
        `a1:(cm_slot_d)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm arithmetic = mp_rule(spec_rule(
        `ilength (a1:(cm_slot_d)list)`,
        int_arith_rule(
          `!n:int. 0i <= n ==>
             ~(1i + n == 0i) && (1i + n) - 1i == n`)),
        tail_nonnegative);
    gnode reduced = CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv, THM_LIST(
          get_theorem_by_name("APPEND"),
          get_theorem_by_name("ILENGTH_DEF"),
          get_cm_slots_prefix_def(), get_cm_slots_size_def(),
          tail_nonnegative,
          conjunct1_rule(arithmetic), conjunct2_rule(arithmetic)));
    ENSURE_COND(!IS_NULL(reduced->solved),
        "slot-prefix append step remains open: %s",
        cstr_gnode(reduced));
  }
  return gnode_prove(root);
err:
  return empty_theorem;
}
PROOF thm cm_slots_prefix_append = cm_prove_slots_prefix_append();

PROOF static thm cm_prove_slots_size_snoc(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (prefix:(cm_slot_d)list)
         (slot:cm_slot_d).
         cm_slots_size structs (prefix ++ [slot]) ==
         cm_slots_size structs prefix + cm_slot_size structs slot`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs, `prefix:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    gnode reduced = CONV_TAC(
        leaf, reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("APPEND"), get_cm_slots_size_def(),
          int_arith_rule(`!x:int. x + 0i == 0i + x`))));
    ENSURE_COND(!IS_NULL(reduced->solved),
        "slot-size snoc base remains open: %s",
        cstr_gnode(reduced));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode reduced = CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv, THM_LIST(
          get_theorem_by_name("APPEND"), get_cm_slots_size_def(),
          int_arith_rule(
            `!(x:int) (y:int) (z:int).
               x + (y + z) == (x + y) + z`)));
    ENSURE_COND(!IS_NULL(reduced->solved),
        "slot-size snoc step remains open: %s",
        cstr_gnode(reduced));
  }
  return gnode_prove(root);
err:
  return empty_theorem;
}
PROOF thm cm_slots_size_snoc = cm_prove_slots_size_snoc();

PROOF static thm cm_prove_param_count_length_bound(void) {
  gnode root = gnode_new_with_ccl(
      `!(params:(cm_slot_d)list).
         ilength params <= cm_param_stores_count params`);
  gnode_list cases = INDUCT_TAC(root, `params:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    gnode reduced = CONV_TAC(
        leaf, reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"),
          get_cm_param_stores_count_def(),
          int_arith_rule(`0i <= 0i`))));
    ENSURE_COND(!IS_NULL(reduced->solved),
        "parameter count-length base remains open: %s",
        cstr_gnode(reduced));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm normalize_nonnegative = spec_rule(
        `cm_slot_ty (a0:cm_slot_d)`,
        cm_char_normalize_nonnegative);
    thm bound = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `ilength (a1:(cm_slot_d)list)`,
        `cm_param_stores_count (a1:(cm_slot_d)list)`,
        `cm_char_normalize_count
           (cm_slot_ty (a0:cm_slot_d))`),
        int_arith_rule(
          `!(a:int) b c.
             a <= b ==> 0i <= c ==> 1i + a <= (b + c) + 5i`)),
        assume_rule(
          `ilength (a1:(cm_slot_d)list) <=
           cm_param_stores_count a1`)),
        normalize_nonnegative);
    gnode reduced = CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv, THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"),
          get_cm_param_stores_count_def(),
          normalize_nonnegative, bound));
    if (IS_NULL(reduced->solved)) {
      thm facts = conj_rule(
          assume_rule(
            `ilength (a1:(cm_slot_d)list) <=
             cm_param_stores_count a1`),
          normalize_nonnegative);
      ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
          concl(facts), goal_ccl(reduced->g))), facts));
    }
    ENSURE_COND(!IS_NULL(reduced->solved),
        "parameter count-length step remains open: %s",
        cstr_gnode(reduced));
  }
  return gnode_prove(root);
err:
  return empty_theorem;
}
PROOF thm cm_param_count_length_bound =
    cm_prove_param_count_length_bound();

PROOF static thm cm_prove_emit_slots_wf_head(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (head:cm_slot_d)
          (tail:(cm_slot_d)list).
         cm_slots_wf structs (head :: tail) ==>
         cm_slot_wf structs head`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm all_wf = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slots_wf_def())), assume_rule(
        `cm_slots_wf (structs:(cm_struct_d)list)
          ((head:cm_slot_d) :: (tail:(cm_slot_d)list))`));
  thm tail_nonnegative = ispec_rule(
      `tail:(cm_slot_d)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm head_bound = by_defs_arith(
      `0i < ilength ((head:cm_slot_d) :: (tail:(cm_slot_d)list))`,
      THM_LIST(get_theorem_by_name("ILENGTH_DEF")),
      THM_LIST(tail_nonnegative));
  thm result = match_mp_rule(match_mp_rule(
      spec_rule(`0i`, all_wf), int_arith_rule(`0i <= 0i`)),
      head_bound);
  ACCEPT_TAC(leaf, conv_rule(rewrite_conv(THM_LIST(
      ispecl_rule(TERM_LIST(
        `head:cm_slot_d`, `tail:(cm_slot_d)list`),
        cm_inth_zero_cons))), result));
  return gnode_prove(root);
}
PROOF static thm cm_emit_slots_wf_head =
    cm_prove_emit_slots_wf_head();

PROOF static thm cm_prove_emit_slots_wf_tail(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (head:cm_slot_d)
          (tail:(cm_slot_d)list).
         cm_slots_wf structs (head :: tail) ==>
         cm_slots_wf structs tail`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm all_wf = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slots_wf_def())), assume_rule(
        `cm_slots_wf (structs:(cm_struct_d)list)
          ((head:cm_slot_d) :: (tail:(cm_slot_d)list))`));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      get_cm_slots_wf_def())));
  gnode with_index = GEN_TAC(opened, "tail_index");
  gnode tail_leaf = AUTO_INTROS_TAC(with_index);
  thm tail_nonnegative = assume_rule(`0i <= (tail_index:int)`);
  thm tail_upper = assume_rule(
      `(tail_index:int) < ilength (tail:(cm_slot_d)list)`);
  thm full_lower = mp_rule(int_arith_rule(
      `0i <= (tail_index:int) ==> 0i <= tail_index + 1i`),
      tail_nonnegative);
  thm normalized_full_upper = mp_rule(int_arith_rule(mk_imp(
      concl(tail_upper),
      `(tail_index:int) + 1i <
       1i + ilength (tail:(cm_slot_d)list)`)), tail_upper);
  thm full_upper = eq_mp_rule(sym_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
      `(tail_index:int) + 1i < ilength
        ((head:cm_slot_d) :: (tail:(cm_slot_d)list))`)),
      normalized_full_upper);
  thm full_wf = match_mp_rule(match_mp_rule(
      spec_rule(`(tail_index:int) + 1i`, all_wf), full_lower),
      full_upper);
  thm one = mp_rule(int_arith_rule(
      `0i <= (tail_index:int) ==> 1i <= tail_index + 1i`),
      tail_nonnegative);
  thm at_tail = mp_rule(ispecl_rule(TERM_LIST(
      `head:cm_slot_d`, `tail:(cm_slot_d)list`,
      `(tail_index:int) + 1i`), cm_inth_cons_tail), one);
  thm index_exact = int_arith_rule(
      `((tail_index:int) + 1i) - 1i == tail_index`);
  ACCEPT_TAC(tail_leaf, conv_rule(reduce_rewrite_conv(
      THM_LIST(at_tail, index_exact)), full_wf));
  return gnode_prove(root);
}
PROOF static thm cm_emit_slots_wf_tail =
    cm_prove_emit_slots_wf_tail();

PROOF static void cm_function_retarget_call_result64(
    const term cell, const thm result) {
  struct dest_eq_results sides = dest_eq(concl(result));
  add_fact_st(result);
  cst_set_symbolic_state(retarget_cell64_st(
      cst_get_symbolic_state(), cell, sides.tm1, sides.tm2));
}

PROOF static thm cm_emit_params_tail_def = new_fun_definition(
    `cm_emit_params_tail (params:(cm_slot_d)list) :
       (cm_slot_d)list = TL params`);
PROOF static int _e_cm_emit_params_tail =
    cst_add_const_to_header(`cm_emit_params_tail`);

PROOF static thm cm_emit_params_head_def = new_fun_definition(
    `cm_emit_params_head (params:(cm_slot_d)list) :
       cm_slot_d = HD params`);
PROOF static int _e_cm_emit_params_head =
    cst_add_const_to_header(`cm_emit_params_head`);

static void cmc_emit_param_stores_from(
    struct cm_slot *param, int slot, long long offset,
    struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `fid:int`,
                 `structs:(cm_struct_d)list`,
                 `full:(cm_slot_d)list`, `prefix:(cm_slot_d)list`,
                 `params:(cm_slot_d)list`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(structs == cm_program_structs p) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(full == cm_function_params f) **
       fact(full == prefix ++ params) **
       fact(slot == ilength prefix) **
       fact(offset == 8i + cm_slots_size structs prefix) **
       fact(0i <= slot) **
       fact(slot + ilength params <= 2147483647i) **
       fact(0i <= offset) **
       fact(offset + cm_slots_size structs params <= 1048584i) **
       fact(cm_slots_wf structs params <=> true) **
       fact(cm_rep_members_safe params <=> true) **
       fact(cm_param_counts_representable params <=> true) **
       cm_slot_list_rep param params **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_emit_param_stores p fid slot params ++ tail)`)]]
    [[cst::ensure(
      `fact(structs == cm_program_structs p) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(full == cm_function_params f) **
       fact(full == prefix ++ params) **
       fact(slot == ilength prefix) **
       fact(offset == 8i + cm_slots_size structs prefix) **
       fact(0i <= slot) **
       fact(slot + ilength params <= 2147483647i) **
       fact(0i <= offset) **
       fact(offset + cm_slots_size structs params <= 1048584i) **
       fact(cm_slots_wf structs params <=> true) **
       fact(cm_rep_members_safe params <=> true) **
       fact(cm_param_counts_representable params <=> true) **
       cm_slot_list_rep param params **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_emit_param_stores p fid slot params) tail`)]]
{
  if (param == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`param__pre:addr`,
                `params:(cm_slot_d)list`),
              get_cm_slot_null()),
            assume_rule(`param__pre == 0i`))));
      thm params_equal = assume_rule(
          `params == ([]:(cm_slot_d)list)`);
      thm code_shape = by_rewrite(
          `cm_emit_param_stores (p:cm_program) (fid:int)
             (slot__pre:int) (params:(cm_slot_d)list) ==
           ([]:(tvm_inst)list)`,
          THM_LIST(params_equal, get_cm_emit_param_stores_def()));
      cm_select_code_plan_st(code_shape);
      thm nil_view = spec_rule(`param__pre:addr`,
          conjunct1_rule(get_cm_slot_list_rep_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
      substitute_st(sym_rule(ispec_rule(
          `done:(tvm_inst)list`,
          get_theorem_by_name("APPEND_NIL"))));
      thm prefix_shape = beta_norm(ap_term_rule(
          `\code:(tvm_inst)list. (done:(tvm_inst)list) ++ code`,
          sym_rule(code_shape)));
      substitute_st(prefix_shape);
      substitute_st(sym_rule(params_equal));
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    }
    return;
  } else {
    [[cst::proof]] {
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        mp_rule(specl_rule(
            TERM_LIST(`param__pre:addr`,
              `params:(cm_slot_d)list`),
            get_cm_slot_unfold()),
          assume_rule(`~(param__pre == 0i)`))));
    thm params_equal = assume_rule(
        `params == (slot_:cm_slot_d) ::
          (rest_:(cm_slot_d)list)`);
    thm represented = conv_rule(rewrite_conv(THM_LIST(
        params_equal, get_cm_param_counts_representable_def())),
        from_state_bool(
          `cm_param_counts_representable
            (params:(cm_slot_d)list)`));
    thm head_shape = by_rewrite(
        `cm_emit_params_head (params:(cm_slot_d)list) ==
         (slot_:cm_slot_d)`,
        THM_LIST(params_equal, cm_emit_params_head_def,
          get_theorem_by_name("HD")));
    thm tail_shape = by_rewrite(
        `cm_emit_params_tail (params:(cm_slot_d)list) ==
         (rest_:(cm_slot_d)list)`,
        THM_LIST(params_equal, cm_emit_params_tail_def,
          get_theorem_by_name("TL")));
    add_fact_st(head_shape);
    add_fact_st(tail_shape);
    add_fact_st(eqt_intro_rule(
        conjunct1_rule(conjunct2_rule(represented))));
    add_fact_st(eqt_intro_rule(
        conjunct2_rule(conjunct2_rule(represented))));
    thm safe = conv_rule(rewrite_conv(THM_LIST(
        params_equal, get_cm_rep_members_safe_def(),
        get_cm_rep_members_size_def())),
        from_state_bool(
          `cm_rep_members_safe (params:(cm_slot_d)list)`));
    add_fact_st(conjunct1_rule(safe));
    add_fact_st(conjunct1_rule(conjunct2_rule(safe)));
    add_fact_st(eqt_intro_rule(
        conjunct2_rule(conjunct2_rule(conjunct2_rule(safe)))));
    thm all_wf = conv_rule(rewrite_conv(THM_LIST(params_equal)),
        from_state_bool(
          `cm_slots_wf (structs:(cm_struct_d)list)
             (params:(cm_slot_d)list)`));
    thm head_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `slot_:cm_slot_d`,
        `rest_:(cm_slot_d)list`), cm_emit_slots_wf_head), all_wf);
    thm rest_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `slot_:cm_slot_d`,
        `rest_:(cm_slot_d)list`), cm_emit_slots_wf_tail), all_wf);
    add_fact_st(eqt_intro_rule(head_wf));
    add_fact_st(eqt_intro_rule(rest_wf));
    thm code_shape = by_rewrite(
        `cm_emit_param_stores (p:cm_program) (fid:int)
           (slot__pre:int) (params:(cm_slot_d)list) ==
         cm_emit_param_stores p fid (slot__pre + 1i)
           (rest_:(cm_slot_d)list) ++
         cm_char_normalize_code (cm_slot_ty (slot_:cm_slot_d)) ++
         cm_fp_relative_address_code
           (cm_param_offset p fid slot__pre) ++
         cm_store_code (cm_slot_ty slot_)`,
        THM_LIST(params_equal, get_cm_emit_param_stores_def()));
    cm_select_code_plan_st(code_shape);
    }
  }

  long long member_size = cmc_code_slot_size(param->ty, param->count);
  [[cst::proof]] {
    thm head_wf = from_state_bool(
        `cm_slot_wf (structs:(cm_struct_d)list)
           (slot_:cm_slot_d)`);
    thm size_bridge = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `slot_:cm_slot_d`),
        cm_rep_member_size_matches), head_wf);
    thm concrete = assume_rule(
        `(retval:int) ==
         cm_rep_code_slot_size
           (cm_type_encode (cm_slot_ty (slot_:cm_slot_d)))
           (cm_slot_count slot_)`);
    thm rep_shape = inst_rule(TERM_PAIR_LIST(
        (term_pair){`slot_:cm_slot_d`, `member:cm_slot_d`}),
        get_cm_rep_member_size_def());
    thm model = trans_rule(concrete,
        trans_rule(sym_rule(rep_shape), size_bridge));
    cm_function_retarget_call_result64(
        `member_size__addr:addr`, model);
    thm params_equal = assume_rule(
        `params == (slot_:cm_slot_d) ::
          (rest_:(cm_slot_d)list)`);
    thm current_bound = conv_rule(rewrite_conv(THM_LIST(
        params_equal, get_cm_slots_size_def())),
        assume_rule(
          `(offset__pre:int) +
             cm_slots_size (structs:(cm_struct_d)list)
               (params:(cm_slot_d)list) <= 1048584i`));
    thm rest_nonnegative = assume_rule(
        `0i <= cm_rep_members_size
          (rest_:(cm_slot_d)list)`);
    thm rest_size = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`,
        `rest_:(cm_slot_d)list`),
        cm_rep_members_size_matches),
        from_state_bool(
          `cm_slots_wf (structs:(cm_struct_d)list)
             (rest_:(cm_slot_d)list)`));
    thm rest_model_nonnegative = conv_rule(
        rewrite_conv(THM_LIST(rest_size)), rest_nonnegative);
    thm head_model_nonnegative = conv_rule(
        rewrite_conv(THM_LIST(size_bridge)),
        assume_rule(
          `0i <= cm_rep_member_size (slot_:cm_slot_d)`));
    thm offset_nonnegative = assume_rule(
        `0i <= (offset__pre:int)`);
    thm arithmetic = conj_rule(current_bound,
        conj_rule(rest_model_nonnegative,
          conj_rule(offset_nonnegative, head_model_nonnegative)));
    thm next_bounds = mp_rule(int_arith_rule(mk_imp(
        concl(arithmetic),
        `0i <= (offset__pre:int) +
             cm_slot_size (structs:(cm_struct_d)list)
               (slot_:cm_slot_d) &&
         offset__pre + cm_slot_size structs slot_ <= 1048584i`)),
        arithmetic);
    add_fact_st(conjunct1_rule(next_bounds));
    add_fact_st(conjunct2_rule(next_bounds));
    add_fact_st(mp_rule(int_arith_rule(mk_imp(
        concl(next_bounds),
        `--9223372036854775808i <=
             (offset__pre:int) +
               cm_slot_size (structs:(cm_struct_d)list)
                 (slot_:cm_slot_d) &&
         offset__pre + cm_slot_size structs slot_ <=
             9223372036854775807i`)), next_bounds));
  }
  struct cm_slot *next = param->next;

  [[cst::proof]] {
    thm params_equal = assume_rule(
        `params == (slot_:cm_slot_d) ::
          (rest_:(cm_slot_d)list)`);
    thm slot_bound = conv_rule(rewrite_conv(THM_LIST(
        params_equal, get_theorem_by_name("ILENGTH_DEF"))),
        assume_rule(
          `(slot__pre:int) + ilength (params:(cm_slot_d)list) <=
           2147483647i`));
    thm rest_nonnegative = ispec_rule(
        `rest_:(cm_slot_d)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm slot_nonnegative = assume_rule(`0i <= (slot__pre:int)`);
    thm slot_inputs = conj_rule(slot_bound,
        conj_rule(slot_nonnegative, rest_nonnegative));
    thm next_slot_facts = mp_rule(int_arith_rule(mk_imp(
        concl(slot_inputs),
        `0i <= (slot__pre:int) + 1i &&
         slot__pre + 1i + ilength (rest_:(cm_slot_d)list) <=
           2147483647i &&
         --2147483648i <= slot__pre + 1i &&
         slot__pre + 1i <= 2147483647i`)),
        slot_inputs);
    add_fact_st(conjunct1_rule(next_slot_facts));
    add_fact_st(conjunct1_rule(conjunct2_rule(next_slot_facts)));
    add_fact_st(conjunct1_rule(conjunct2_rule(
        conjunct2_rule(next_slot_facts))));
    add_fact_st(conjunct2_rule(conjunct2_rule(
        conjunct2_rule(next_slot_facts))));

    thm prefix_next = conv_rule(
        rewrite_conv(THM_LIST(get_theorem_by_name("APPEND"))),
        sym_rule(ispecl_rule(TERM_LIST(
            `prefix:(cm_slot_d)list`,
            `[slot_:cm_slot_d]`,
            `rest_:(cm_slot_d)list`),
          get_theorem_by_name("APPEND_ASSOC"))));
    thm full_next = trans_rule(
        assume_rule(
          `full ==
           (prefix:(cm_slot_d)list) ++
             (params:(cm_slot_d)list)`),
        trans_rule(beta_norm(ap_term_rule(
            `\xs:(cm_slot_d)list.
               (prefix:(cm_slot_d)list) ++ xs`,
            params_equal)),
          sym_rule(prefix_next)));
    add_fact_st(full_next);
    thm next_prefix_length = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"),
          int_arith_rule(`!x:int. x + (1i + 0i) == x + 1i`))),
        ispecl_rule(TERM_LIST(
            `prefix:(cm_slot_d)list`, `[slot_:cm_slot_d]`),
          get_theorem_by_name("ILENGTH_APPEND")));
    thm next_slot_model = trans_rule(
        beta_norm(ap_term_rule(`\x:int. x + 1i`,
          assume_rule(
            `(slot__pre:int) ==
             ilength (prefix:(cm_slot_d)list)`))),
        sym_rule(next_prefix_length));
    add_fact_st(next_slot_model);
    thm next_offset_model = by_rewrite(
        `(offset__pre:int) +
           cm_slot_size (structs:(cm_struct_d)list)
             (slot_:cm_slot_d) ==
         8i + cm_slots_size structs (prefix ++ [slot_])`,
        THM_LIST(assume_rule(
            `(offset__pre:int) ==
             8i + cm_slots_size
               (structs:(cm_struct_d)list)
               (prefix:(cm_slot_d)list)`),
          cm_slots_size_snoc,
          int_arith_rule(
            `!(a:int) b c. (a + b) + c == a + (b + c)`)));
    add_fact_st(next_offset_model);
    thm current_bound = conv_rule(rewrite_conv(THM_LIST(
        params_equal, get_cm_slots_size_def())),
        assume_rule(
          `(offset__pre:int) +
             cm_slots_size (structs:(cm_struct_d)list)
               (params:(cm_slot_d)list) <= 1048584i`));
    thm next_total = mp_rule(int_arith_rule(mk_imp(
        concl(current_bound),
        `(offset__pre:int) +
             cm_slot_size (structs:(cm_struct_d)list)
               (slot_:cm_slot_d) +
             cm_slots_size structs (rest_:(cm_slot_d)list) <=
           1048584i`)), current_bound);
    add_fact_st(next_total);
  }
  [[cst::proof]] {
    substitute_st(sym_rule(assume_rule(
        `cm_emit_params_head (params:(cm_slot_d)list) ==
         (slot_:cm_slot_d)`)));
    substitute_st(sym_rule(assume_rule(
        `cm_emit_params_tail (params:(cm_slot_d)list) ==
         (rest_:(cm_slot_d)list)`)));
  }

  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`fid`, `(fid:int)`)]]
  [[cst::where(`structs`, `(structs:(cm_struct_d)list)`)]]
  [[cst::where(`full`, `(full:(cm_slot_d)list)`)]]
  [[cst::where(`prefix`,
               `(prefix:(cm_slot_d)list) ++
                 [cm_emit_params_head
                    (params:(cm_slot_d)list)]`)]]
  [[cst::where(`params`,
               `cm_emit_params_tail
                  (params:(cm_slot_d)list)`)]]
  cmc_emit_param_stores_from(next, slot + 1,
                             offset + member_size, emitter);

  [[cst::proof]] {
    thm function_equal = assume_rule(
        `(f:cm_function_d) ==
         inth (fid:int) (cm_program_functions (p:cm_program))`);
    thm params_equal = beta_norm(ap_term_rule(
        `\fn:cm_function_d. cm_function_params fn`,
        function_equal));
    thm function_params = assume_rule(
        `full == cm_function_params (f:cm_function_d)`);
    thm decomposed = assume_rule(
        `full ==
         (prefix:(cm_slot_d)list) ++
           (params:(cm_slot_d)list)`);
    thm model_params = trans_rule(sym_rule(params_equal),
        trans_rule(sym_rule(function_params), decomposed));
    thm prefix_congruence = beta_norm(ap_term_rule(
        `\xs:(cm_slot_d)list.
           cm_slots_prefix (structs:(cm_struct_d)list) xs
             (ilength (prefix:(cm_slot_d)list))`,
        model_params));
    thm prefix_model = trans_rule(prefix_congruence,
        ispecl_rule(TERM_LIST(
            `structs:(cm_struct_d)list`,
            `prefix:(cm_slot_d)list`,
            `params:(cm_slot_d)list`),
          cm_slots_prefix_append));
    thm param_model = by_rewrite(
        `cm_param_offset (p:cm_program) (fid:int)
           (slot__pre:int) ==
         8i + cm_slots_size (structs:(cm_struct_d)list)
           (prefix:(cm_slot_d)list)`,
        THM_LIST(
          get_cm_param_offset_def(), prefix_model,
          assume_rule(
            `structs == cm_program_structs (p:cm_program)`),
          assume_rule(
            `(slot__pre:int) ==
             ilength (prefix:(cm_slot_d)list)`)));
    thm offset_exact = trans_rule(assume_rule(
        `(offset__pre:int) ==
         8i + cm_slots_size (structs:(cm_struct_d)list)
           (prefix:(cm_slot_d)list)`), sym_rule(param_model));
    add_fact_st(offset_exact);
    substitute_st(sym_rule(offset_exact));
    add_fact_st(offset_exact);
  }

  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`model_ty`,
               `cm_slot_ty
                  (cm_emit_params_head
                    (params:(cm_slot_d)list))`)]]
  cm_emit_normalize_plan(emitter, param->ty);
  cm_emit_fp_address_plan(emitter, offset);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`model_ty`,
               `cm_slot_ty
                  (cm_emit_params_head
                    (params:(cm_slot_d)list))`)]]
  cm_emit_store_plan(emitter, param->ty);

  [[cst::proof]] {
    thm params_equal = assume_rule(
        `params ==
         cm_emit_params_head (params:(cm_slot_d)list) ::
         cm_emit_params_tail params`);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        mp_rule(specl_rule(TERM_LIST(`param__pre:addr`,
            `cm_emit_params_head (params:(cm_slot_d)list)`,
            `cm_emit_params_tail (params:(cm_slot_d)list)`,
            `zn_:int`), get_cm_slot_fold()),
          assume_rule(`~(param__pre == 0i)`))));
    substitute_st(sym_rule(params_equal));
    thm parameter_congruence = beta_norm(ap_term_rule(
        `\xs:(cm_slot_d)list.
           cm_emit_param_stores (p:cm_program) (fid:int)
             (slot__pre:int) xs`,
        params_equal));
    thm unfolded = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `slot__pre:int`,
        `cm_emit_params_head (params:(cm_slot_d)list)`,
        `cm_emit_params_tail (params:(cm_slot_d)list)`),
        conjunct2_rule(get_cm_emit_param_stores_def()));
    thm code_shape = trans_rule(parameter_congruence, unfolded);
    thm concrete_shape = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(assume_rule(
          `(offset__pre:int) ==
           cm_param_offset (p:cm_program) (fid:int)
             (slot__pre:int)`)))), code_shape);
    cm_restore_code_plan_st(concrete_shape);
  }
}

PROOF static thm cm_prove_emit_members_safe_bounds(void) {
  gnode root = gnode_new_with_ccl(
      `!(slots:(cm_slot_d)list).
         cm_rep_members_safe slots ==>
         0i <= cm_rep_members_size slots &&
         cm_rep_members_size slots <= 1048576i`);
  gnode_list cases = INDUCT_TAC(root, `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_members_safe_def(),
        get_cm_rep_members_size_def(),
        int_arith_rule(`0i <= 0i && 0i <= 1048576i`))));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode reduced = CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv, THM_LIST(
          get_cm_rep_members_safe_def(),
          get_cm_rep_members_size_def()));
    if (IS_NULL(reduced->solved)) {
      thm safe = conv_rule(rewrite_conv(THM_LIST(
          get_cm_rep_members_safe_def())),
          assume_rule(
            `cm_rep_members_safe
              ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`));
      thm head_nonnegative = conjunct1_rule(safe);
      thm rest_nonnegative =
          conjunct1_rule(conjunct2_rule(safe));
      thm upper = conv_rule(
          rewrite_conv(THM_LIST(get_cm_rep_members_size_def())),
          conjunct1_rule(conjunct2_rule(conjunct2_rule(safe))));
      thm facts = conj_rule(head_nonnegative,
          conj_rule(rest_nonnegative, upper));
      ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
          concl(facts), goal_ccl(reduced->g))), facts));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_emit_members_safe_bounds =
    cm_prove_emit_members_safe_bounds();

PROOF static thm cm_prove_param_counts_total(void) {
  gnode root = gnode_new_with_ccl(
      `!(params:(cm_slot_d)list).
         cm_param_counts_representable params ==>
         cm_i32_code_count (cm_param_stores_count params)`);
  gnode_list cases = INDUCT_TAC(root, `params:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_param_counts_representable_def(),
        get_cm_param_stores_count_def(),
        get_cm_i32_code_count_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm represented = conv_rule(rewrite_conv(THM_LIST(
        get_cm_param_counts_representable_def())),
        assume_rule(
          `cm_param_counts_representable
            ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`));
    ACCEPT_TAC(leaf, conjunct1_rule(represented));
  }
  return gnode_prove(root);
}
PROOF static thm cm_param_counts_total =
    cm_prove_param_counts_total();

PROOF static thm cm_emit_empty_slots_def = new_fun_definition(
    `cm_emit_empty_slots (unit:int) : (cm_slot_d)list =
       ([]:(cm_slot_d)list)`);
PROOF static int _e_cm_emit_empty_slots =
    cst_add_const_to_header(`cm_emit_empty_slots`);

static void cmc_emit_prologue(
    struct cm_function *fn, int fid, struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`,
                 `s:cm_stmt`, `body:int`, `next:int`,
                 `structs:(cm_struct_d)list`,
                 `out:int`, `capacity:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`)]]
    [[cst::require(
      `fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(s == cm_function_body f) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe
              (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe
              (cm_function_locals f) <=> true) **
       fact(cm_rep_stmt_temps_safe s <=> true) **
       fact(8i + cm_rep_members_size (cm_function_params f) +
              cm_rep_members_size (cm_function_locals f) +
              8i * cm_stemps s <= 2147483647i) **
       fact(cm_param_counts_representable
              (cm_function_params f) <=> true) **
       cm_function_context_rep fn f body next **
       cm_stmt_rep body s **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_emit_prologue p fid ++ tail)`)]]
    [[cst::ensure(
      `fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(s == cm_function_body f) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe
              (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe
              (cm_function_locals f) <=> true) **
       fact(cm_rep_stmt_temps_safe s <=> true) **
       fact(8i + cm_rep_members_size (cm_function_params f) +
              cm_rep_members_size (cm_function_locals f) +
              8i * cm_stemps s <= 2147483647i) **
       fact(cm_param_counts_representable
              (cm_function_params f) <=> true) **
       cm_function_context_rep fn f body next **
       cm_stmt_rep body s **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_emit_prologue p fid) tail`)]]
{
  [[cst::proof]] { cm_open_function_context_st(); }
  [[cst::where(`params`, `cm_function_params (f:cm_function_d)`)]]
  [[cst::where(`locals`, `cm_function_locals (f:cm_function_d)`)]]
  [[cst::where(`body`, `(s:cm_stmt)`)]]
  long long frame_size = cmc_frame_size(fn);
  [[cst::proof]] {
    thm params_match = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`,
        `cm_function_params (f:cm_function_d)`),
        cm_rep_members_size_matches), from_state_bool(
          `cm_slots_wf structs (cm_function_params f)`));
    thm locals_match = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`,
        `cm_function_locals (f:cm_function_d)`),
        cm_rep_members_size_matches), from_state_bool(
          `cm_slots_wf structs (cm_function_locals f)`));
    thm returned = assume_rule(
        `(retval:int) ==
         8i + cm_rep_members_size (cm_function_params f) +
           cm_rep_members_size (cm_function_locals f) +
           8i * cm_stemps (s:cm_stmt)`);
    thm frame_model = by_rewrite(
        `8i + cm_rep_members_size (cm_function_params f) +
           cm_rep_members_size (cm_function_locals f) +
           8i * cm_stemps (s:cm_stmt) ==
         cm_frame_size (cm_program_structs (p:cm_program)) f`,
        THM_LIST(params_match, locals_match,
          assume_rule(`structs == cm_program_structs (p:cm_program)`),
          assume_rule(`s == cm_function_body (f:cm_function_d)`),
          get_cm_frame_size_def(), get_cm_temp_slots_def()));
    cm_retarget_i64_st(`frame_size__addr:addr`,
        trans_rule(returned, frame_model));
    thm code_shape = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_emit_prologue_def(),
          sym_rule(assume_rule(
            `f == inth (fid__pre:int)
              (cm_program_functions (p:cm_program))`)),
          get_theorem_by_name("APPEND"))),
        `cm_emit_prologue (p:cm_program) (fid__pre:int)`);
    cm_select_code_plan_st(code_shape);
    rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    cm_add_opcode_facts_st(`0i`, `TVMPushOp`);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMPushOp`)]]
  cm_emit_plan(emitter, CMC_OP_PUSH, 8);
  [[cst::proof]] { cm_add_opcode_facts_st(`4i`, `TVMLoadOp`); }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMLoadOp`)]]
  cm_emit_plan(emitter, CMC_OP_LOAD, 0);
  [[cst::proof]] { cm_add_opcode_facts_st(`2i`, `TVMDupOp`); }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMDupOp`)]]
  cm_emit_plan(emitter, CMC_OP_DUP, 0);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMPushOp`)]]
  cm_emit_plan(emitter, CMC_OP_PUSH, frame_size);
  [[cst::proof]] { cm_add_opcode_facts_st(`9i`, `TVMSubOp`); }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMSubOp`)]]
  cm_emit_plan(emitter, CMC_OP_SUB, 0);
  [[cst::proof]] { cm_add_opcode_facts_st(`5i`, `TVMStoreOp`); }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMStoreOp`)]]
  cm_emit_plan(emitter, CMC_OP_STORE, 0);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMPushOp`)]]
  cm_emit_plan(emitter, CMC_OP_PUSH, 8);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMLoadOp`)]]
  cm_emit_plan(emitter, CMC_OP_LOAD, 0);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMPushOp`)]]
  cm_emit_plan(emitter, CMC_OP_PUSH, frame_size);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMSubOp`)]]
  cm_emit_plan(emitter, CMC_OP_SUB, 0);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMDupOp`)]]
  cm_emit_plan(emitter, CMC_OP_DUP, 0);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMPushOp`)]]
  cm_emit_plan(emitter, CMC_OP_PUSH, 8);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMStoreOp`)]]
  cm_emit_plan(emitter, CMC_OP_STORE, 0);
  [[cst::proof]] { cm_add_opcode_facts_st(`1i`, `TVMPopOp`); }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMPopOp`)]]
  cm_emit_plan(emitter, CMC_OP_POP, 0);
  [[cst::proof]] {
    thm represented = mp_rule(spec_rule(
        `cm_function_params (f:cm_function_d)`,
        cm_param_counts_total), from_state_bool(
          `cm_param_counts_representable
            (cm_function_params f)`));
    thm count_bounds = conv_rule(
        rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
        represented);
    thm length_bound = spec_rule(
        `cm_function_params (f:cm_function_d)`,
        cm_param_count_length_bound);
    thm slot_upper = mp_rule(
        mp_rule(int_arith_rule(
          `ilength (cm_function_params (f:cm_function_d)) <=
             cm_param_stores_count (cm_function_params f) ==>
           cm_param_stores_count (cm_function_params f) <=
             2147483647i ==>
           0i + ilength (cm_function_params f) <= 2147483647i`),
          length_bound), conjunct2_rule(count_bounds));
    add_fact_st(slot_upper);
    thm safe_bounds = mp_rule(spec_rule(
        `cm_function_params (f:cm_function_d)`,
        cm_emit_members_safe_bounds), from_state_bool(
          `cm_rep_members_safe (cm_function_params f)`));
    thm size_match = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`,
        `cm_function_params (f:cm_function_d)`),
        cm_rep_members_size_matches), from_state_bool(
          `cm_slots_wf structs (cm_function_params f)`));
    thm size_bounds = conv_rule(rewrite_conv(THM_LIST(size_match)),
        safe_bounds);
    add_fact_st(mp_rule(int_arith_rule(
        `cm_slots_size structs (cm_function_params (f:cm_function_d))
             <= 1048576i ==>
         8i + cm_slots_size structs (cm_function_params f)
             <= 1048584i`),
        conjunct2_rule(size_bounds)));
    add_fact_st(int_arith_rule(
        `0i <= 0i && 0i <= 2147483647i`));
    add_fact_st(by_rewrite(
        `cm_function_params (f:cm_function_d) ==
         cm_emit_empty_slots 0i ++ cm_function_params f`,
        THM_LIST(cm_emit_empty_slots_def,
          get_theorem_by_name("APPEND"))));
    add_fact_st(by_defs_arith(
        `0i == ilength (cm_emit_empty_slots 0i)`,
        THM_LIST(cm_emit_empty_slots_def,
          get_theorem_by_name("ILENGTH_DEF")), THM_LIST()));
    add_fact_st(by_defs_arith(
        `8i == 8i +
           cm_slots_size structs (cm_emit_empty_slots 0i)`,
        THM_LIST(cm_emit_empty_slots_def,
          get_cm_slots_size_def()), THM_LIST()));
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`fid`, `(fid__pre:int)`)]]
  [[cst::where(`structs`, `(structs:(cm_struct_d)list)`)]]
  [[cst::where(`full`,
                `cm_function_params (f:cm_function_d)`)]]
  [[cst::where(`prefix`, `cm_emit_empty_slots 0i`)]]
  [[cst::where(`params`,
                `cm_function_params (f:cm_function_d)`)]]
  cmc_emit_param_stores_from(fn->params, 0, 8, emitter);
  [[cst::proof]] {
    thm code_shape = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_emit_prologue_def(),
          sym_rule(assume_rule(
            `f == inth (fid__pre:int)
              (cm_program_functions (p:cm_program))`)),
          get_theorem_by_name("APPEND"))),
        `cm_emit_prologue (p:cm_program) (fid__pre:int)`);
    rewrite_st(THM_LIST(
        cm_emit_empty_slots_def,
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("APPEND"),
        get_cm_slots_size_def()));
    cm_close_function_context_st();
    cm_restore_code_plan_st(code_shape);
  }
}

void cmc_emit_function(
    struct cm_program *program, struct cm_function *fn,
    int fid, int function_pc, struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`,
                 `s:cm_stmt`, `body:int`, `next:int`,
                 `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(s == cm_function_body f) **
       fact(function_pc == cm_function_pc p fid) **
       fact(cm_stmt_wf p f false s <=> true) **
       fact(cm_stmt_counts_representable p fid s <=> true) **
       fact(cm_param_counts_representable
              (cm_function_params f) <=> true) **
       fact(cm_i32_code_count
              (cm_function_prologue_count f) <=> true) **
       fact(cm_i32_code_count function_pc <=> true) **
       fact(cm_i32_code_count
              (cm_function_pc p fid +
               cm_function_prologue_count f) <=> true) **
       fact(cm_i32_code_count
              ((cm_function_pc p fid +
                cm_function_prologue_count f) +
               ilength
                 (cm_emit_stmt p fid
                   (cm_function_pc p fid +
                    cm_function_prologue_count f)
                   0i 0i 0i s)) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe
              (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe
              (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe
              (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe
              (cm_function_locals f) <=> true) **
       fact(cm_rep_stmt_temps_safe s <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <=
              1048560i) **
       fact(8i + cm_rep_members_size (cm_function_params f) +
              cm_rep_members_size (cm_function_locals f) +
              8i * cm_stemps s <= 2147483647i) **
       fact(cm_temp_offset p fid (cm_stemps s) <=
              2147483647i) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_stmt_rep body s **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_emit_function p fid ++ tail)`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(s == cm_function_body f) **
       fact(function_pc == cm_function_pc p fid) **
       fact(cm_stmt_wf p f false s <=> true) **
       fact(cm_stmt_counts_representable p fid s <=> true) **
       fact(cm_param_counts_representable
              (cm_function_params f) <=> true) **
       fact(cm_i32_code_count
              (cm_function_prologue_count f) <=> true) **
       fact(cm_i32_code_count function_pc <=> true) **
       fact(cm_i32_code_count
              (cm_function_pc p fid +
               cm_function_prologue_count f) <=> true) **
       fact(cm_i32_code_count
              ((cm_function_pc p fid +
                cm_function_prologue_count f) +
               ilength
                 (cm_emit_stmt p fid
                   (cm_function_pc p fid +
                    cm_function_prologue_count f)
                   0i 0i 0i s)) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe
              (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe
              (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe
              (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe
              (cm_function_locals f) <=> true) **
       fact(cm_rep_stmt_temps_safe s <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <=
              1048560i) **
       fact(8i + cm_rep_members_size (cm_function_params f) +
              cm_rep_members_size (cm_function_locals f) +
              8i * cm_stemps s <= 2147483647i) **
       fact(cm_temp_offset p fid (cm_stemps s) <=
              2147483647i) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_stmt_rep body s **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_emit_function p fid) tail`)]]
{
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`body`, `(body:int)`)]]
  [[cst::where(`next`, `(next:int)`)]]
  int prologue_count = cmc_function_prologue_count(fn);
  [[cst::proof]] {
    cm_retarget_stmt_call_result_st(
        `prologue_count__addr:addr`,
        assume_rule(
          `(retval:int) ==
           cm_function_prologue_count (f:cm_function_d)`));
    substitute_st(assume_rule(
        `(function_pc__pre:int) ==
         cm_function_pc (p:cm_program) (fid__pre:int)`));
    cm_add_i32_term_st(from_state_bool(
        `cm_i32_code_count
          (cm_function_pc (p:cm_program) (fid__pre:int) +
           cm_function_prologue_count (f:cm_function_d))`));
  }
  int body_pc = function_pc + prologue_count;
  struct cm_stmt *body_stmt;
  [[cst::proof]] { cm_open_function_context_st(); }
  body_stmt = fn->body;
  [[cst::proof]] { cm_close_function_context_st(); }
  [[cst::where(`s`, `(s:cm_stmt)`)]]
  int temp_limit = cmc_stmt_temps(body_stmt);
  [[cst::proof]] {
    cm_retarget_stmt_call_result_st(
        `temp_limit__addr:addr`,
        assume_rule(
          `(retval_1:int) == cm_stemps (s:cm_stmt)`));
    thm code_shape = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_emit_function_def(),
          sym_rule(assume_rule(
            `f == inth (fid__pre:int)
              (cm_program_functions (p:cm_program))`)),
          sym_rule(assume_rule(
            `s == cm_function_body (f:cm_function_d)`)),
          get_theorem_by_name("APPEND"))),
        `cm_emit_function (p:cm_program) (fid__pre:int)`);
    cm_select_code_plan_st(code_shape);
    rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`s`, `(s:cm_stmt)`)]]
  [[cst::where(`structs`,
                `cm_program_structs (p:cm_program)`)]]
  cmc_emit_prologue(fn, fid, emitter);
  [[cst::proof]] {
    thm nonnegative = assume_rule(
        `0i <= cm_stemps (s:cm_stmt)`);
    add_fact_st(mp_rule(int_arith_rule(
        `0i <= cm_stemps (s:cm_stmt) ==>
         0i <= 0i && 0i <= cm_stemps s &&
         0i + cm_stemps s <= cm_stemps s`), nonnegative));
    thm zero_i32 = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_i32_code_count_def())),
        `cm_i32_code_count 0i`));
    add_fact_st(eqt_intro_rule(zero_i32));
  }
  [[cst::proof]] {
    thm function_at = assume_rule(
        `f == inth (fid__pre:int)
          (cm_program_functions (p:cm_program))`);
    thm prologue_at = ap_term_rule(
        `cm_function_prologue_count:cm_function_d->int`,
        function_at);
    thm body_start_at = conv_rule(
        rewrite_conv(THM_LIST(prologue_at)),
        from_state_bool(
          `cm_i32_code_count
            (cm_function_pc (p:cm_program) (fid__pre:int) +
             cm_function_prologue_count (f:cm_function_d))`));
    add_fact_st(eqt_intro_rule(body_start_at));
    thm body_end_at = conv_rule(
        rewrite_conv(THM_LIST(prologue_at,
          assume_rule(
            `s == cm_function_body (f:cm_function_d)`))),
        from_state_bool(
          `cm_i32_code_count
            ((cm_function_pc (p:cm_program) (fid__pre:int) +
              cm_function_prologue_count (f:cm_function_d)) +
             ilength
               (cm_emit_stmt p fid__pre
                 (cm_function_pc p fid__pre +
                  cm_function_prologue_count f)
                 0i 0i 0i (s:cm_stmt)))`));
    add_fact_st(eqt_intro_rule(body_end_at));
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`s`, `(s:cm_stmt)`)]]
  [[cst::where(`loop_`, `false`)]]
  cmc_emit_stmt(program, fid, fn, body_pc, 0, temp_limit,
                0, 0, body_stmt, emitter);
  [[cst::proof]] {
    rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    cm_add_opcode_facts_st(`0i`, `TVMPushOp`);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMPushOp`)]]
  cm_emit_plan(emitter, CMC_OP_PUSH, 0);
  [[cst::where(`p`, `(p:cm_program)`)]]
  cm_emit_return_epilogue_plan(emitter);
  [[cst::proof]] {
    thm code_shape = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_emit_function_def(),
          sym_rule(assume_rule(
            `f == inth (fid__pre:int)
              (cm_program_functions (p:cm_program))`)),
          sym_rule(assume_rule(
            `s == cm_function_body (f:cm_function_d)`)),
          get_theorem_by_name("APPEND"))),
        `cm_emit_function (p:cm_program) (fid__pre:int)`);
    cm_restore_code_plan_st(code_shape);
  }
}
