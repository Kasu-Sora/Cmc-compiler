#include "cmc_concrete_emit_expr_call.h"
#include "cmc_concrete_emit_plan.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_emit_plan.c"


PROOF static thm cm_args_tail_def = new_fun_definition(
    `cm_args_tail (args:(cm_expr)list) : (cm_expr)list = TL args`);
PROOF static int _e_cm_args_tail =
    cst_add_const_to_header(`cm_args_tail`);

PROOF static thm cm_args_head_def = new_fun_definition(
    `cm_args_head (args:(cm_expr)list) : cm_expr = HD args`);
PROOF static int _e_cm_args_head =
    cst_add_const_to_header(`cm_args_head`);

PROOF static thm cm_call_slots_tail_def = new_fun_definition(
    `cm_call_slots_tail (slots:(cm_slot_d)list) :
       (cm_slot_d)list = TL slots`);
PROOF static int _e_cm_call_slots_tail =
    cst_add_const_to_header(`cm_call_slots_tail`);


PROOF static thm cm_prove_rep_args_length_matches_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(args:(cm_expr)list).
         cm_rep_args_length args == ilength args`);
  gnode_list cases = INDUCT_TAC(root, `args:(cm_expr)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_args_length_def(),
        get_theorem_by_name("ILENGTH_DEF"))));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        get_cm_rep_args_length_def(),
        get_theorem_by_name("ILENGTH_DEF")));
  }
  return gnode_prove(root);
}
PROOF static thm cm_rep_args_length_matches_length =
    cm_prove_rep_args_length_matches_length();

PROOF static thm cm_prove_args_depth_nonnegative(void) {
  gnode root = gnode_new_with_ccl(
      `!(args:(cm_expr)list).
         0i <= cm_adepth (cm_args_apair args)`);
  gnode_list cases = INDUCT_TAC(root, `args:(cm_expr)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_expr_tpair_def(), get_cm_adepth_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm head_nonnegative = conv_rule(rewrite_conv(THM_LIST(
        get_cm_rtemps_def())), conjunct2_rule(spec_rule(
          `a0:cm_expr`, cm_expr_temps_nonnegative)));
    thm bound = specl_rule(TERM_LIST(
        `cm_tright (cm_expr_tpair (a0:cm_expr))`,
        `cm_adepth (cm_args_apair (a1:(cm_expr)list))`),
        cm_imax_left_bound);
    gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        get_cm_expr_tpair_def(), get_cm_adepth_def())));
    ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
        mk_conj(concl(head_nonnegative), concl(bound)),
        goal_ccl(reduced->g))), conj_rule(head_nonnegative, bound)));
  }
  return gnode_prove(root);
}
PROOF static thm cm_args_depth_nonnegative =
    cm_prove_args_depth_nonnegative();

PROOF static thm cm_prove_rep_args_safe_from_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(args:(cm_expr)list).
         ilength args <= 2147483647i ==>
         cm_rep_args_safe args`);
  gnode_list cases = INDUCT_TAC(root, `args:(cm_expr)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_args_safe_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm tail_nonnegative = ispec_rule(
        `a1:(cm_expr)list`, get_theorem_by_name("ILENGTH_NONNEG"));
    thm cons_bound = conv_rule(rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
        assume_rule(
          `ilength ((a0:cm_expr) :: (a1:(cm_expr)list)) <=
           2147483647i`));
    thm tail_bound = mp_rule(int_arith_rule(
        `1i + ilength (a1:(cm_expr)list) <= 2147483647i ==>
         ilength a1 <= 2147483647i`), cons_bound);
    thm ih = mp_rule(assume_rule(
        `ilength (a1:(cm_expr)list) <= 2147483647i ==>
         cm_rep_args_safe a1`), tail_bound);
    gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        get_cm_rep_args_safe_def(),
        cm_rep_args_length_matches_length)));
    thm facts = conj_rule(tail_nonnegative,
        conj_rule(mp_rule(int_arith_rule(
            `1i + ilength (a1:(cm_expr)list) <= 2147483647i ==>
             ilength a1 < 2147483647i`), cons_bound), ih));
    ACCEPT_TAC(reduced, facts);
  }
  return gnode_prove(root);
}
PROOF static thm cm_rep_args_safe_from_length =
    cm_prove_rep_args_safe_from_length();

PROOF static thm cm_prove_call_rep_members_size_nonnegative(void) {
  gnode root = gnode_new_with_ccl(
      `!(members:(cm_slot_d)list).
         cm_rep_members_safe members ==>
         0i <= cm_rep_members_size members`);
  gnode_list cases = INDUCT_TAC(root, `members:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_members_size_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm safe = conv_rule(rewrite_conv(THM_LIST(
        get_cm_rep_members_safe_def())),
        assume_rule(
          `cm_rep_members_safe
            ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`));
    gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        get_cm_rep_members_size_def())));
    thm inputs = conj_rule(conjunct1_rule(safe),
        conjunct1_rule(conjunct2_rule(safe)));
    ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
        concl(inputs), goal_ccl(reduced->g))), inputs));
  }
  return gnode_prove(root);
}
PROOF static thm cm_call_rep_members_size_nonnegative =
    cm_prove_call_rep_members_size_nonnegative();

PROOF static void cm_call_add_temp_limit_facts_st(void) {
  term params = `cm_function_params (f:cm_function_d)`;
  term locals = `cm_function_locals (f:cm_function_d)`;
  thm params_safe = from_state_bool(
      `cm_rep_members_safe
        (cm_function_params (f:cm_function_d))`);
  thm locals_safe = from_state_bool(
      `cm_rep_members_safe
        (cm_function_locals (f:cm_function_d))`);
  thm params_rep_nonnegative = mp_rule(
      spec_rule(params, cm_call_rep_members_size_nonnegative),
      params_safe);
  thm locals_rep_nonnegative = mp_rule(
      spec_rule(locals, cm_call_rep_members_size_nonnegative),
      locals_safe);
  thm params_match = mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`, params),
      cm_rep_members_size_matches), from_state_bool(
        `cm_slots_wf (cm_program_structs (p:cm_program))
          (cm_function_params (f:cm_function_d))`));
  thm locals_match = mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`, locals),
      cm_rep_members_size_matches), from_state_bool(
        `cm_slots_wf (cm_program_structs (p:cm_program))
          (cm_function_locals (f:cm_function_d))`));
  thm params_nonnegative = by_rewrite(
      `0i <= cm_slots_size (cm_program_structs (p:cm_program))
        (cm_function_params (f:cm_function_d))`,
      THM_LIST(sym_rule(params_match), params_rep_nonnegative));
  thm locals_nonnegative = by_rewrite(
      `0i <= cm_slots_size (cm_program_structs (p:cm_program))
        (cm_function_locals (f:cm_function_d))`,
      THM_LIST(sym_rule(locals_match), locals_rep_nonnegative));
  thm params_at_fid = conv_rule(rewrite_conv(THM_LIST(
      assume_rule(
        `(f:cm_function_d) ==
         inth (fid__pre:int) (cm_program_functions (p:cm_program))`))),
      params_nonnegative);
  thm locals_at_fid = conv_rule(rewrite_conv(THM_LIST(
      assume_rule(
        `(f:cm_function_d) ==
         inth (fid__pre:int) (cm_program_functions (p:cm_program))`))),
      locals_nonnegative);
  thm offset_bound = conv_rule(rewrite_conv(THM_LIST(
      get_cm_temp_offset_def())), assume_rule(
        `cm_temp_offset (p:cm_program) (fid__pre:int)
          (temp_limit__pre:int) <= 2147483647i`));
  thm limit_upper = by_defs_arith(
      `(temp_limit__pre:int) <= 2147483647i`,
      THM_LIST(get_cm_temp_offset_def()),
      THM_LIST(params_at_fid, locals_at_fid, offset_bound));
  thm limit_nonnegative = mp_rule(mp_rule(int_arith_rule(
      `0i <= (temp__pre:int) ==>
       temp__pre <= (temp_limit__pre:int) ==>
       0i <= temp_limit__pre`),
      assume_rule(`0i <= (temp__pre:int)`)),
      assume_rule(`(temp__pre:int) <= (temp_limit__pre:int)`));
  add_fact_st(limit_nonnegative);
  add_fact_st(limit_upper);
  add_fact_st(mp_rule(mp_rule(spec_rule(
      `temp_limit__pre:int`, cm_nonnegative_i32_cast),
      limit_nonnegative), limit_upper));
}

PROOF static void cm_call_add_temp_offset_bound_st(const term at) {
  term at_le_limit = subst(TERM_PAIR_LIST(
      (term_pair){at, `at_:int`}),
      `(at_:int) <= (temp_limit__pre:int)`);
  thm monotone = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, at, `temp_limit__pre:int`),
      cm_temp_offset_mono), assume_rule(at_le_limit));
  term ceiling = `cm_temp_offset (p:cm_program) (fid:int)
      (temp_limit__pre:int) <= 2147483647i`;
  term target = subst(TERM_PAIR_LIST(
      (term_pair){at, `at_:int`}),
      `cm_temp_offset (p:cm_program) (fid:int)
         (at_:int) <= 2147483647i`);
  thm result = mp_rule(mp_rule(
      int_arith_rule(mk_imp(concl(monotone),
        mk_imp(ceiling, target))), monotone),
      assume_rule(ceiling));
  add_fact_st(result);
}

PROOF static thm cm_call_code_shape(const thm shape,
                                    const thm lvalue_case,
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
        get_cm_lcode_of_def(), cm_expr_code_for_def,
        get_cm_emit_rvalue_def(), get_cm_emit_lvalue_def(),
        lvalue_case, eqf_intro_rule(int_arith_rule(`~(1i == 0i)`)),
        get_theorem_by_name("APPEND_NIL"))));
}

PROOF static void cm_open_call_payload_st(const thm shape) {
  thm payload_view = by_rewrite(
      `cm_expr_payload (e:cm_expr)
         (za:int) (zb:int) (zargs:int) -|-
       fact(za == 0i && zb == 0i) **
       cm_arg_list_rep zargs (args_:(cm_expr)list)`,
      THM_LIST(shape, get_cm_expr_payload_def(),
        get_cm_arg_list_rep_def()));
  apply_hconv_st(eq2ent(payload_view));
}

PROOF static void cm_close_call_payload_st(const thm shape) {
  thm payload_view = by_rewrite(
      `cm_expr_payload (e:cm_expr)
         (za:int) (zb:int) (zargs:int) -|-
       fact(za == 0i && zb == 0i) **
       cm_arg_list_rep zargs (args_:(cm_expr)list)`,
      THM_LIST(shape, get_cm_expr_payload_def(),
        get_cm_arg_list_rep_def()));
  thm payload_facts = conj_rule(
      assume_rule(`(za:int) == 0i`),
      assume_rule(`(zb:int) == 0i`));
  thm payload_intro = frame_right_slrule(
      add_fact_hconv(payload_facts),
      `cm_arg_list_rep (zargs:int) (args_:(cm_expr)list)`);
  apply_hconv_st(trans_slrule(payload_intro,
      eq2ent(sym_rule(payload_view))));
}

static void cm_emit_args_reload_plan(struct cm_function *fn, int slot,
                                     int temp_limit, struct cm_arg *arg,
                                     struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `fid:int`,
                 `args:(cm_expr)list`, `body:int`, `next:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= slot) **
       fact(slot + ilength args <= temp_limit) **
       fact(0i <= temp_limit) **
       fact(temp_limit <= 2147483647i) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       cm_function_context_rep fn f body next **
       cm_arg_list_rep arg args **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_emit_args_reload p fid slot args ++ tail)`)]]
    [[cst::ensure(
      `fact(0i <= slot) **
       fact(slot + ilength args <= temp_limit) **
       fact(0i <= temp_limit) **
       fact(temp_limit <= 2147483647i) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       cm_function_context_rep fn f body next **
       cm_arg_list_rep arg args **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_emit_args_reload p fid slot args) tail`)]]
{
  if (arg == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`arg__pre:addr`, `args:(cm_expr)list`),
              get_cm_arg_null()),
            assume_rule(`arg__pre == 0i`))));
      thm args_equal = assume_rule(
          `args == ([]:(cm_expr)list)`);
      thm code_shape = by_rewrite(
          `cm_emit_args_reload (p:cm_program) (fid:int)
             (slot__pre:int) (args:(cm_expr)list) ==
           ([]:(tvm_inst)list)`,
          THM_LIST(args_equal, get_cm_emit_args_reload_def()));
      cm_select_code_plan_st(code_shape);
      thm nil_view = by_rewrite(
          `cm_arg_list_rep (arg__pre:int)
              ([]:(cm_expr)list) -|-
           fact(arg__pre == 0i)`,
          THM_LIST(get_cm_arg_list_rep_def(),
            get_cm_expr_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
      substitute_st(sym_rule(ispec_rule(
          `done:(tvm_inst)list`,
          get_theorem_by_name("APPEND_NIL"))));
      thm prefix_shape = beta_norm(ap_term_rule(
          `\code:(tvm_inst)list. (done:(tvm_inst)list) ++ code`,
          sym_rule(code_shape)));
      substitute_st(prefix_shape);
      substitute_st(sym_rule(args_equal));
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    }
    return;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`arg__pre:addr`, `args:(cm_expr)list`),
              get_cm_arg_unfold()),
            assume_rule(`~(arg__pre == 0i)`))));
      thm args_equal = assume_rule(
          `args == (arg_:cm_expr) :: (rest_:(cm_expr)list)`);
      thm total_bound = conv_rule(rewrite_conv(THM_LIST(
          args_equal, get_theorem_by_name("ILENGTH_DEF"))),
          assume_rule(
            `(slot__pre:int) + ilength (args:(cm_expr)list) <=
             (temp_limit__pre:int)`));
      add_fact_st(total_bound);
      thm tail_shape = by_rewrite(
          `cm_args_tail (args:(cm_expr)list) ==
           (rest_:(cm_expr)list)`,
          THM_LIST(args_equal, cm_args_tail_def,
            get_theorem_by_name("TL")));
      add_fact_st(tail_shape);
      thm slot_nonnegative = assume_rule(`0i <= (slot__pre:int)`);
      thm rest_nonnegative = ispec_rule(
          `rest_:(cm_expr)list`,
          get_theorem_by_name("ILENGTH_NONNEG"));
      thm limit_upper =
          assume_rule(`(temp_limit__pre:int) <= 2147483647i`);
      thm slot_bound = mp_rule(int_arith_rule(
          `(slot__pre:int) + 1i +
               ilength (rest_:(cm_expr)list) <=
             (temp_limit__pre:int) ==>
           0i <= ilength rest_ ==>
           slot__pre <= temp_limit__pre`), total_bound);
      slot_bound = mp_rule(slot_bound, rest_nonnegative);
      add_fact_st(slot_bound);
      cm_call_add_temp_offset_bound_st(`slot__pre:int`);
      thm next_nonnegative = mp_rule(int_arith_rule(
          `0i <= (slot__pre:int) ==> 0i <= slot__pre + 1i`),
          slot_nonnegative);
      thm next_upper = mp_rule(mp_rule(mp_rule(int_arith_rule(
          `(slot__pre:int) + 1i +
               ilength (rest_:(cm_expr)list) <=
             (temp_limit__pre:int) ==>
           0i <= ilength rest_ ==>
           temp_limit__pre <= 2147483647i ==>
           slot__pre + 1i <= 2147483647i`),
          total_bound), rest_nonnegative), limit_upper);
      add_fact_st(next_nonnegative);
      add_fact_st(next_upper);
      add_fact_st(mp_rule(mp_rule(spec_rule(
          `(slot__pre:int) + 1i`, cm_nonnegative_i32_cast),
          next_nonnegative), next_upper));
      thm code_shape = by_rewrite(
          `cm_emit_args_reload (p:cm_program) (fid:int)
             (slot__pre:int) (args:(cm_expr)list) ==
           cm_temp_load_code p fid slot__pre ++
           cm_emit_args_reload p fid (slot__pre + 1i)
             (rest_:(cm_expr)list)`,
          THM_LIST(args_equal, get_cm_emit_args_reload_def()));
      cm_select_code_plan_st(code_shape);
      substitute_st(sym_rule(tail_shape));
    }
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`fid`, `(fid:int)`)]]
  [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
  cm_emit_temp_load_plan(fn, slot, emitter);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`fid`, `(fid:int)`)]]
  [[cst::where(`args`, `cm_args_tail (args:(cm_expr)list)`)]]
  cm_emit_args_reload_plan(fn, slot + 1, temp_limit,
                           arg->next, emitter);
  [[cst::proof]] {
    thm args_equal = assume_rule(
        `args == (arg_:cm_expr) :: (rest_:(cm_expr)list)`);
    thm tail_shape = by_rewrite(
        `cm_args_tail (args:(cm_expr)list) ==
         (rest_:(cm_expr)list)`,
        THM_LIST(args_equal, cm_args_tail_def,
          get_theorem_by_name("TL")));
    thm cons_shape = by_rewrite(
        `args ==
         (arg_:cm_expr) :: cm_args_tail (args:(cm_expr)list)`,
        THM_LIST(args_equal, tail_shape));
    thm expr_view = inst_rule(TERM_PAIR_LIST(
        (term_pair){`ze_:int`, `p:int`},
        (term_pair){`arg_:cm_expr`, `e:cm_expr`}),
        get_cm_expr_rep_def());
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        eq2ent(expr_view)));
    thm tail_view = inst_rule(TERM_PAIR_LIST(
        (term_pair){`zn_:int`, `p:int`},
        (term_pair){`cm_args_tail (args:(cm_expr)list)`,
                    `args:(cm_expr)list`}),
        get_cm_arg_list_rep_def());
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        eq2ent(tail_view)));
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        mp_rule(specl_rule(TERM_LIST(`arg__pre:addr`,
            `arg_:cm_expr`, `cm_args_tail (args:(cm_expr)list)`,
            `ze_:int`, `zn_:int`), get_cm_arg_fold()),
          assume_rule(`~(arg__pre == 0i)`))));
    substitute_st(sym_rule(cons_shape));
    thm code_shape = by_rewrite(
        `cm_emit_args_reload (p:cm_program) (fid:int)
           (slot__pre:int) (args:(cm_expr)list) ==
         cm_temp_load_code p fid slot__pre ++
         cm_emit_args_reload p fid (slot__pre + 1i)
           (cm_args_tail (args:(cm_expr)list))`,
        THM_LIST(args_equal, tail_shape,
          get_cm_emit_args_reload_def()));
    cm_restore_code_plan_st(code_shape);
  }
}

PROOF static thm cm_call_rvalue_code_length_at(
    const term expr, const term pc, const term temp) {
  thm lengths = conjunct2_rule(
      spec_rule(expr, get_cm_expr_code_lengths()));
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid__pre:int`, pc, temp), lengths);
  term selection_target = subst(TERM_PAIR_LIST(
      (term_pair){expr, `expr_:cm_expr`},
      (term_pair){pc, `pc_:int`},
      (term_pair){temp, `temp_:int`}),
      `cm_expr_code_for (p:cm_program) (fid__pre:int)
         (pc_:int) (temp_:int) (expr_:cm_expr) 0i ==
       cm_emit_rvalue p fid__pre pc_ temp_ expr_`);
  thm selection = by_rewrite(selection_target, THM_LIST(
      cm_expr_code_for_def,
      eqt_intro_rule(int_arith_rule(`0i == 0i`))));
  return conv_rule(rewrite_conv(THM_LIST(gsym_rule(selection))),
      result);
}

PROOF static void cm_call_add_store_pc_facts(
    const thm code_shape) {
  term head_code =
      `cm_expr_code_for (p:cm_program) (fid__pre:int)
         (pc__pre:int) (scratch__pre:int) (arg_:cm_expr) 0i`;
  term rest_code =
      `cm_emit_args_store (p:cm_program) (fid__pre:int)
         ((pc__pre:int) +
           cm_rvalue_code_count p fid__pre (arg_:cm_expr) + 5i)
         ((slot__pre:int) + 1i) (scratch__pre:int)
         (rest_:(cm_expr)list)`;
  term after_head =
      `cm_temp_store_code (p:cm_program) (fid__pre:int)
         (slot__pre:int) ++
       cm_emit_args_store p fid__pre
         (pc__pre +
           cm_rvalue_code_count p fid__pre (arg_:cm_expr) + 5i)
         (slot__pre + 1i) scratch__pre
         (rest_:(cm_expr)list)`;
  thm parent_pc = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
      eqt_elim_rule(assume_rule(
        `cm_i32_code_count (pc__pre:int) <=> true`)));
  thm parent_end = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
      eqt_elim_rule(assume_rule(
        `cm_i32_code_count
          ((pc__pre:int) + ilength
            (cm_emit_args_store (p:cm_program) (fid__pre:int)
              pc__pre (slot__pre:int) (scratch__pre:int)
              (args:(cm_expr)list))) <=> true`)));
  thm head_length = cm_call_rvalue_code_length_at(
      `arg_:cm_expr`, `pc__pre:int`, `scratch__pre:int`);
  thm after_head_nonnegative = ispec_rule(
      after_head, get_theorem_by_name("ILENGTH_NONNEG"));
  thm rest_nonnegative = ispec_rule(
      rest_code, get_theorem_by_name("ILENGTH_NONNEG"));
  thm head_nonnegative = ispec_rule(
      head_code, get_theorem_by_name("ILENGTH_NONNEG"));
  thm_list rules = THM_LIST(
      get_cm_i32_code_count_def(), code_shape,
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("ILENGTH_DEF"),
      get_cm_temp_store_code_def(),
      get_cm_fp_relative_address_code_def(), head_length);
  thm parent_end_shape =
      conv_rule(rewrite_conv(rules), parent_end);
  thm after_head_nonnegative_shape =
      conv_rule(rewrite_conv(rules), after_head_nonnegative);
  thm rest_nonnegative_shape =
      conv_rule(rewrite_conv(rules), rest_nonnegative);
  thm head_end = by_defs_arith(
      `cm_i32_code_count
        ((pc__pre:int) + ilength
          (cm_expr_code_for (p:cm_program) (fid__pre:int)
            pc__pre (scratch__pre:int) (arg_:cm_expr) 0i))`,
      rules, THM_LIST(parent_pc, parent_end_shape,
        after_head_nonnegative_shape, head_nonnegative,
        head_length));
  thm next_start = by_defs_arith(
      `cm_i32_code_count
        ((pc__pre:int) +
          cm_rvalue_code_count (p:cm_program)
            (fid__pre:int) (arg_:cm_expr) + 5i)`,
      rules, THM_LIST(parent_pc, parent_end_shape,
        rest_nonnegative_shape, head_nonnegative, head_length));
  thm next_bounds = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
      next_start);
  thm partial = by_defs_arith(
      `cm_i32_code_count
        ((pc__pre:int) +
          cm_rvalue_code_count (p:cm_program)
            (fid__pre:int) (arg_:cm_expr))`,
      rules, THM_LIST(parent_pc, next_bounds,
        head_nonnegative, head_length));
  thm partial_bounds = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
      partial);
  thm tail_end = by_defs_arith(
      `cm_i32_code_count
        (((pc__pre:int) +
           cm_rvalue_code_count (p:cm_program)
             (fid__pre:int) (arg_:cm_expr) + 5i) +
         ilength
           (cm_emit_args_store p fid__pre
             (pc__pre +
               cm_rvalue_code_count p fid__pre arg_ + 5i)
             (slot__pre + 1i) (scratch__pre:int)
             (rest_:(cm_expr)list)))`,
      rules, THM_LIST(parent_pc, next_bounds,
        parent_end_shape, rest_nonnegative_shape,
        head_nonnegative, head_length));
  add_fact_st(eqt_intro_rule(head_end));
  add_fact_st(eqt_intro_rule(next_start));
  add_fact_st(eqt_intro_rule(partial));
  add_fact_st(eqt_intro_rule(tail_end));
  add_fact_st(conjunct1_rule(partial_bounds));
  add_fact_st(conjunct2_rule(partial_bounds));
  add_fact_st(conjunct1_rule(next_bounds));
  add_fact_st(conjunct2_rule(next_bounds));
  add_fact_st(mp_rule(mp_rule(spec_rule(
      `(pc__pre:int) +
        cm_rvalue_code_count (p:cm_program)
          (fid__pre:int) (arg_:cm_expr)`,
      cm_nonnegative_i32_cast), conjunct1_rule(partial_bounds)),
      conjunct2_rule(partial_bounds)));
  add_fact_st(mp_rule(mp_rule(spec_rule(
      `(pc__pre:int) +
        cm_rvalue_code_count (p:cm_program)
          (fid__pre:int) (arg_:cm_expr) + 5i`,
      cm_nonnegative_i32_cast), conjunct1_rule(next_bounds)),
      conjunct2_rule(next_bounds)));
}

static void cm_emit_args_store_plan(struct cm_program *program, int fid,
                                    struct cm_function *fn, int pc,
                                    int slot, int scratch, int temp_limit,
                                    struct cm_arg *arg,
                                    struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`,
                 `args:(cm_expr)list`, `slots:(cm_slot_d)list`,
                 `body:int`, `next:int`, `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_args_wf p f args slots <=> true) **
       fact(cm_args_counts_representable p fid args <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= slot) **
       fact(slot + ilength args == scratch) **
       fact(0i <= scratch) ** fact(scratch <= temp_limit) **
       fact(scratch + cm_adepth (cm_args_apair args) <=
              temp_limit) **
       fact(0i <= temp_limit) **
       fact(temp_limit <= 2147483647i) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength
                (cm_emit_args_store p fid pc slot scratch args))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_arg_list_rep arg args **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_emit_args_store p fid pc slot scratch args ++ tail)`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_args_wf p f args slots <=> true) **
       fact(cm_args_counts_representable p fid args <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= slot) **
       fact(slot + ilength args == scratch) **
       fact(0i <= scratch) ** fact(scratch <= temp_limit) **
       fact(scratch + cm_adepth (cm_args_apair args) <=
              temp_limit) **
       fact(0i <= temp_limit) **
       fact(temp_limit <= 2147483647i) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength
                (cm_emit_args_store p fid pc slot scratch args))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_arg_list_rep arg args **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_emit_args_store p fid pc slot scratch args)
         tail`)]]
{
  if (arg == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`arg__pre:addr`, `args:(cm_expr)list`),
              get_cm_arg_null()),
            assume_rule(`arg__pre == 0i`))));
      thm args_equal = assume_rule(
          `args == ([]:(cm_expr)list)`);
      thm code_shape = by_rewrite(
          `cm_emit_args_store (p:cm_program) (fid__pre:int)
             (pc__pre:int) (slot__pre:int) (scratch__pre:int)
             (args:(cm_expr)list) ==
           ([]:(tvm_inst)list)`,
          THM_LIST(args_equal, get_cm_emit_expr_pair_def()));
      thm length_shape = by_rewrite(
          `ilength
             (cm_emit_args_store (p:cm_program) (fid__pre:int)
               (pc__pre:int) (slot__pre:int) (scratch__pre:int)
               (args:(cm_expr)list)) == 0i`,
          THM_LIST(code_shape, get_theorem_by_name("ILENGTH_DEF")));
      rewrite_st(THM_LIST(length_shape));
      cm_select_code_plan_st(code_shape);
      thm nil_view = by_rewrite(
          `cm_arg_list_rep (arg__pre:int)
              ([]:(cm_expr)list) -|-
           fact(arg__pre == 0i)`,
          THM_LIST(get_cm_arg_list_rep_def(),
            get_cm_expr_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
      substitute_st(sym_rule(ispec_rule(
          `done:(tvm_inst)list`,
          get_theorem_by_name("APPEND_NIL"))));
      thm prefix_shape = beta_norm(ap_term_rule(
          `\code:(tvm_inst)list. (done:(tvm_inst)list) ++ code`,
          sym_rule(code_shape)));
      substitute_st(prefix_shape);
      substitute_st(sym_rule(args_equal));
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND"),
        get_theorem_by_name("ILENGTH_DEF")));
      thm restored_end = by_rewrite(
          `cm_i32_code_count
             ((pc__pre:int) +
              ilength
                (cm_emit_args_store (p:cm_program) (fid__pre:int)
                  pc__pre (slot__pre:int) (scratch__pre:int)
                  (args:(cm_expr)list))) <=> true`,
          THM_LIST(args_equal, get_cm_emit_expr_pair_def(),
            get_theorem_by_name("ILENGTH_DEF"),
            from_state_bool(
              `cm_i32_code_count ((pc__pre:int) + 0i)`)));
      add_fact_st(restored_end);
    }
    return;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`arg__pre:addr`, `args:(cm_expr)list`),
              get_cm_arg_unfold()),
            assume_rule(`~(arg__pre == 0i)`))));
      thm args_equal = assume_rule(
          `args == (arg_:cm_expr) :: (rest_:(cm_expr)list)`);
      thm well_formed = conv_rule(rewrite_conv(THM_LIST(
          args_equal, get_cm_args_wf_def(),
          gsym_rule(cm_call_slots_tail_def))),
          from_state_bool(
            `cm_args_wf (p:cm_program) (f:cm_function_d)
              (args:(cm_expr)list) (slots:(cm_slot_d)list)`));
      cm_add_count_facts(well_formed);
      thm representable = conv_rule(rewrite_conv(THM_LIST(
          args_equal, get_cm_args_counts_representable_def())),
          from_state_bool(
            `cm_args_counts_representable
              (p:cm_program) (fid__pre:int)
              (args:(cm_expr)list)`));
      cm_add_count_facts(representable);
    }
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  int head_count =
      cm_expr_rvalue_count_context(program, fid, fn, arg->expr);
  [[cst::proof]] {
    thm args_equal = assume_rule(
        `args == (arg_:cm_expr) :: (rest_:(cm_expr)list)`);
    thm tail_shape = by_rewrite(
        `cm_args_tail (args:(cm_expr)list) ==
         (rest_:(cm_expr)list)`,
        THM_LIST(args_equal, cm_args_tail_def,
          get_theorem_by_name("TL")));
    thm slot_total = conv_rule(rewrite_conv(THM_LIST(
        args_equal, get_theorem_by_name("ILENGTH_DEF"))),
        assume_rule(
          `(slot__pre:int) + ilength (args:(cm_expr)list) ==
           (scratch__pre:int)`));
    thm next_slot_total = mp_rule(int_arith_rule(
        `(slot__pre:int) + (1i + ilength
             (rest_:(cm_expr)list)) == (scratch__pre:int) ==>
         slot__pre + 1i + ilength rest_ == scratch__pre`),
        slot_total);
    add_fact_st(next_slot_total);
    thm rest_length_nonnegative = ispec_rule(
        `rest_:(cm_expr)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm slot_bound = mp_rule(mp_rule(int_arith_rule(
        `(slot__pre:int) + 1i + ilength
             (rest_:(cm_expr)list) == (scratch__pre:int) ==>
         0i <= ilength rest_ ==>
         slot__pre <= scratch__pre`),
        next_slot_total), rest_length_nonnegative);
    thm slot_limit = mp_rule(mp_rule(int_arith_rule(
        `(slot__pre:int) <= (scratch__pre:int) ==>
         scratch__pre <= (temp_limit__pre:int) ==>
         slot__pre <= temp_limit__pre`), slot_bound),
        assume_rule(
          `(scratch__pre:int) <= (temp_limit__pre:int)`));
    add_fact_st(slot_bound);
    add_fact_st(slot_limit);
    cm_add_temp_offset_bound_st(`slot__pre:int`);
    cm_add_temp_offset_bound_st(`scratch__pre:int`);
    thm next_slot_nonnegative = mp_rule(int_arith_rule(
        `0i <= (slot__pre:int) ==> 0i <= slot__pre + 1i`),
        assume_rule(`0i <= (slot__pre:int)`));
    thm next_slot_upper = mp_rule(mp_rule(mp_rule(int_arith_rule(
        `(slot__pre:int) + 1i + ilength
             (rest_:(cm_expr)list) == (scratch__pre:int) ==>
         0i <= ilength rest_ ==>
         scratch__pre <= (temp_limit__pre:int) ==>
         temp_limit__pre <= 2147483647i ==>
         slot__pre + 1i <= 2147483647i`),
        next_slot_total), rest_length_nonnegative),
        assume_rule(
          `(scratch__pre:int) <= (temp_limit__pre:int)`));
    next_slot_upper = mp_rule(next_slot_upper,
        assume_rule(
          `(temp_limit__pre:int) <= 2147483647i`));
    add_fact_st(next_slot_nonnegative);
    add_fact_st(next_slot_upper);
    add_fact_st(mp_rule(mp_rule(spec_rule(
        `(slot__pre:int) + 1i`, cm_nonnegative_i32_cast),
        next_slot_nonnegative), next_slot_upper));
    thm depth_shape = by_rewrite(
        `cm_adepth (cm_args_apair (args:(cm_expr)list)) ==
         cm_imax
           (cm_tright (cm_expr_tpair (arg_:cm_expr)))
           (cm_adepth
             (cm_args_apair (rest_:(cm_expr)list)))`,
        THM_LIST(args_equal, get_cm_expr_tpair_def(),
          get_cm_adepth_def()));
    thm parent_depth_bound = conv_rule(rewrite_conv(THM_LIST(
        depth_shape)), assume_rule(
          `(scratch__pre:int) +
             cm_adepth (cm_args_apair (args:(cm_expr)list)) <=
           (temp_limit__pre:int)`));
    thm head_max = specl_rule(TERM_LIST(
        `cm_tright (cm_expr_tpair (arg_:cm_expr))`,
        `cm_adepth (cm_args_apair
          (rest_:(cm_expr)list))`), cm_imax_left_bound);
    thm rest_max = specl_rule(TERM_LIST(
        `cm_tright (cm_expr_tpair (arg_:cm_expr))`,
        `cm_adepth (cm_args_apair
          (rest_:(cm_expr)list))`), cm_imax_right_bound);
    thm head_temp_bound = by_defs_arith(
        `(scratch__pre:int) +
           cm_expr_temps_for (arg_:cm_expr) 0i <=
         (temp_limit__pre:int)`,
        THM_LIST(cm_expr_temps_for_def, get_cm_rtemps_def()),
        THM_LIST(parent_depth_bound, head_max));
    thm rest_temp_bound = mp_rule(mp_rule(int_arith_rule(
        `(scratch__pre:int) +
             cm_imax
               (cm_tright (cm_expr_tpair (arg_:cm_expr)))
               (cm_adepth
                 (cm_args_apair (rest_:(cm_expr)list))) <=
             (temp_limit__pre:int) ==>
         cm_adepth (cm_args_apair rest_) <=
           cm_imax
             (cm_tright (cm_expr_tpair arg_))
             (cm_adepth (cm_args_apair rest_)) ==>
         scratch__pre + cm_adepth (cm_args_apair rest_) <=
           temp_limit__pre`),
        parent_depth_bound), rest_max);
    add_fact_st(head_temp_bound);
    add_fact_st(rest_temp_bound);
    thm code_shape = by_rewrite(
        `cm_emit_args_store (p:cm_program) (fid__pre:int)
           (pc__pre:int) (slot__pre:int) (scratch__pre:int)
           (args:(cm_expr)list) ==
         cm_expr_code_for p fid__pre pc__pre scratch__pre
           (arg_:cm_expr) 0i ++
         cm_temp_store_code p fid__pre slot__pre ++
         cm_emit_args_store p fid__pre
           (pc__pre +
             cm_rvalue_code_count p fid__pre arg_ + 5i)
           (slot__pre + 1i) scratch__pre
           (rest_:(cm_expr)list)`,
        THM_LIST(args_equal, get_cm_emit_expr_pair_def(),
          cm_expr_code_for_def, get_cm_emit_rvalue_def(),
          eqt_intro_rule(int_arith_rule(`0i == 0i`))));
    cm_call_add_store_pc_facts(code_shape);
    cm_select_code_plan_st(code_shape);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`fid`, `(fid__pre:int)`)]]
  cm_emit_expr(program, fid, fn, pc, scratch, temp_limit,
               arg->expr, 0, emitter);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`fid`, `(fid__pre:int)`)]]
  [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
  cm_emit_temp_store_plan(fn, slot, emitter);
  [[cst::proof]] {
    thm args_equal = assume_rule(
        `args == (arg_:cm_expr) :: (rest_:(cm_expr)list)`);
    thm tail_shape = by_rewrite(
        `cm_args_tail (args:(cm_expr)list) ==
         (rest_:(cm_expr)list)`,
        THM_LIST(args_equal, cm_args_tail_def,
          get_theorem_by_name("TL")));
    thm head_shape = by_rewrite(
        `cm_args_head (args:(cm_expr)list) ==
         (arg_:cm_expr)`,
        THM_LIST(args_equal, cm_args_head_def,
          get_theorem_by_name("HD")));
    substitute_st(sym_rule(head_shape));
    substitute_st(assume_rule(
        `retval ==
         cm_rcount_of
           (cm_expr_code_counts (p:cm_program) (fid__pre:int)
             (cm_args_head (args:(cm_expr)list)))`));
    thm count_shape = inst_rule(TERM_PAIR_LIST(
        (term_pair){`fid__pre:int`, `fid:int`},
        (term_pair){`cm_args_head (args:(cm_expr)list)`,
                    `expr:cm_expr`}),
        get_cm_rvalue_code_count_def());
    substitute_st(sym_rule(count_shape));
    substitute_st(sym_rule(tail_shape));
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(
      `pc`,
      `pc__pre + cm_rvalue_code_count
         (p:cm_program) (fid__pre:int)
         (cm_args_head (args:(cm_expr)list)) + 5i`)]]
  [[cst::where(`slot`, `slot__pre + 1i`)]]
  [[cst::where(`args`, `cm_args_tail (args:(cm_expr)list)`)]]
  [[cst::where(`slots`,
                `cm_call_slots_tail (slots:(cm_slot_d)list)`)]]
  cm_emit_args_store_plan(program, fid, fn,
      pc + head_count + 5, slot + 1, scratch, temp_limit,
      arg->next, emitter);
  [[cst::proof]] {
    thm args_equal = assume_rule(
        `args == (arg_:cm_expr) :: (rest_:(cm_expr)list)`);
    thm tail_shape = by_rewrite(
        `cm_args_tail (args:(cm_expr)list) ==
         (rest_:(cm_expr)list)`,
        THM_LIST(args_equal, cm_args_tail_def,
          get_theorem_by_name("TL")));
    thm head_shape = by_rewrite(
        `cm_args_head (args:(cm_expr)list) ==
         (arg_:cm_expr)`,
        THM_LIST(args_equal, cm_args_head_def,
          get_theorem_by_name("HD")));
    thm cons_shape = by_rewrite(
        `args ==
         cm_args_head (args:(cm_expr)list) ::
           cm_args_tail (args:(cm_expr)list)`,
        THM_LIST(args_equal, head_shape, tail_shape));
    thm expr_view = inst_rule(TERM_PAIR_LIST(
        (term_pair){`ze_:int`, `p:int`},
        (term_pair){`cm_args_head (args:(cm_expr)list)`,
                    `e:cm_expr`}),
        get_cm_expr_rep_def());
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        eq2ent(expr_view)));
    thm tail_view = inst_rule(TERM_PAIR_LIST(
        (term_pair){`zn_:int`, `p:int`},
        (term_pair){`cm_args_tail (args:(cm_expr)list)`,
                    `args:(cm_expr)list`}),
        get_cm_arg_list_rep_def());
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        eq2ent(tail_view)));
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        mp_rule(specl_rule(TERM_LIST(`arg__pre:addr`,
            `cm_args_head (args:(cm_expr)list)`,
            `cm_args_tail (args:(cm_expr)list)`,
            `ze_:int`, `zn_:int`), get_cm_arg_fold()),
          assume_rule(`~(arg__pre == 0i)`))));
    substitute_st(sym_rule(cons_shape));
    thm code_shape = by_rewrite(
        `cm_emit_args_store (p:cm_program) (fid__pre:int)
           (pc__pre:int) (slot__pre:int) (scratch__pre:int)
           (args:(cm_expr)list) ==
         cm_expr_code_for p fid__pre pc__pre scratch__pre
           (cm_args_head (args:(cm_expr)list)) 0i ++
         cm_temp_store_code p fid__pre slot__pre ++
         cm_emit_args_store p fid__pre
           (pc__pre +
             cm_rvalue_code_count p fid__pre
               (cm_args_head (args:(cm_expr)list)) + 5i)
           (slot__pre + 1i) scratch__pre
           (cm_args_tail (args:(cm_expr)list))`,
        THM_LIST(args_equal, head_shape, tail_shape,
          cm_args_head_def, cm_args_tail_def,
          get_theorem_by_name("HD"), get_theorem_by_name("TL"),
          get_cm_emit_expr_pair_def(), cm_expr_code_for_def,
          get_cm_emit_rvalue_def(),
          eqt_intro_rule(int_arith_rule(`0i == 0i`))));
    cm_restore_code_plan_end_st(code_shape);
  }
}

PROOF static void cm_call_add_initial_store_end_st(
    const thm code_shape) {
  thm parent_start = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
      from_state_bool(`cm_i32_code_count (pc__pre:int)`));
  thm parent_end = conv_rule(
      rewrite_conv(THM_LIST(code_shape,
        get_cm_i32_code_count_def(),
        get_theorem_by_name("ILENGTH_APPEND"),
        get_theorem_by_name("ILENGTH_DEF"))),
      from_state_bool(
        `cm_i32_code_count
           ((pc__pre:int) +
            ilength
              (cm_expr_code_for (p:cm_program) (fid__pre:int)
                pc__pre (temp__pre:int) (e:cm_expr)
                (lvalue__pre:int)))`));
  thm store_nonnegative = ispec_rule(
      `cm_emit_args_store (p:cm_program) (fid__pre:int)
         (pc__pre:int) (temp__pre:int)
         (temp__pre + ilength (args_:(cm_expr)list)) args_`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  thm reload_nonnegative = ispec_rule(
      `cm_emit_args_reload (p:cm_program) (fid__pre:int)
         (temp__pre:int) (args_:(cm_expr)list)`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  thm result = by_defs_arith(
      `cm_i32_code_count
         ((pc__pre:int) +
          ilength
            (cm_emit_args_store (p:cm_program) (fid__pre:int)
              pc__pre (temp__pre:int)
              (temp__pre + ilength (args_:(cm_expr)list)) args_))`,
      THM_LIST(get_cm_i32_code_count_def(),
        get_theorem_by_name("ILENGTH_APPEND"),
        get_theorem_by_name("ILENGTH_DEF")),
      THM_LIST(parent_start, parent_end,
        store_nonnegative, reload_nonnegative));
  add_fact_st(eqt_intro_rule(result));
}

PROOF static void cm_call_add_rvalue_temp_facts_st(
    const thm shape, const thm lvalue_case) {
  thm temp_bound = conv_rule(rewrite_conv(THM_LIST(
      shape, lvalue_case, cm_expr_temps_for_def,
      get_cm_rtemps_def(), get_cm_expr_tpair_def(),
      get_cm_tright_def(), cm_args_count_matches_length)),
      assume_rule(
        `(temp__pre:int) +
           cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) <=
         (temp_limit__pre:int)`));
  thm length_nonnegative = ispec_rule(
      `args_:(cm_expr)list`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  thm depth_nonnegative = spec_rule(
      `args_:(cm_expr)list`, cm_args_depth_nonnegative);
  thm limit_upper = assume_rule(
      `(temp_limit__pre:int) <= 2147483647i`);
  thm facts = conj_rule(
      assume_rule(`0i <= (temp__pre:int)`),
      conj_rule(length_nonnegative,
        conj_rule(depth_nonnegative,
          conj_rule(temp_bound, limit_upper))));
  thm scratch_nonnegative = mp_rule(int_arith_rule(mk_imp(
      concl(facts),
      `0i <= (temp__pre:int) +
         ilength (args_:(cm_expr)list)`)), facts);
  thm scratch_bound = mp_rule(int_arith_rule(mk_imp(
      concl(facts),
      `(temp__pre:int) + ilength (args_:(cm_expr)list) <=
       (temp_limit__pre:int)`)), facts);
  thm length_upper = mp_rule(int_arith_rule(mk_imp(
      concl(facts),
      `ilength (args_:(cm_expr)list) <= 2147483647i`)),
      facts);
  thm scratch_upper = mp_rule(int_arith_rule(mk_imp(
      concl(facts),
      `(temp__pre:int) + ilength (args_:(cm_expr)list) <=
       2147483647i`)), facts);
  thm safe = mp_rule(spec_rule(
      `args_:(cm_expr)list`, cm_rep_args_safe_from_length),
      length_upper);
  add_fact_st(temp_bound);
  add_fact_st(scratch_nonnegative);
  add_fact_st(scratch_bound);
  add_fact_st(length_upper);
  add_fact_st(scratch_upper);
  add_fact_st(eqt_intro_rule(safe));
  add_fact_st(mp_rule(mp_rule(spec_rule(
      `(temp__pre:int) + ilength (args_:(cm_expr)list)`,
      cm_nonnegative_i32_cast), scratch_nonnegative),
      scratch_upper));
}

void cm_emit_call_expr(struct cm_program *program, int fid,
                       struct cm_function *fn, int pc, int temp,
                       int temp_limit, struct cm_expr *expr,
                       int lvalue, struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `body:int`, `next:int`, `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(cm_rep_expr_kind e == 8i) **
       fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_expr_temps_for e lvalue <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength (cm_expr_code_for p fid pc temp e lvalue))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_expr_code_for p fid pc temp e lvalue ++ tail)`)]]
    [[cst::ensure(
      `fact(cm_rep_expr_kind e == 8i) **
       fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_expr_temps_for e lvalue <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength (cm_expr_code_for p fid pc temp e lvalue))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_expr_code_for p fid pc temp e lvalue) tail`)]]
{
  [[cst::proof]] {
    cm_open_expr_rep_st();
    thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
        get_cm_expr_call_shape_ent()),
        assume_rule(`cm_rep_expr_kind (e:cm_expr) == 8i`));
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(shape_ent,
          TERM_LIST(`callee_:int`, `args_:(cm_expr)list`,
                    `ty_:cm_type`))));
    thm shape = assume_rule(
        `e == CMCallE (callee_:int)
           (args_:(cm_expr)list) (ty_:cm_type)`);
    cm_open_expr_count_facts(shape);
    thm value_model = by_rewrite(
        `cm_rep_expr_value (e:cm_expr) == (callee_:int)`,
        THM_LIST(shape, get_cm_rep_expr_value_def()));
    substitute_st(value_model);
  }
  if (!lvalue) {
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMCallE (callee_:int)
             (args_:(cm_expr)list) (ty_:cm_type)`);
      thm lvalue_case =
          eqt_intro_rule(assume_rule(`lvalue__pre == 0i`));
      cm_open_call_payload_st(shape);
      cm_call_add_temp_limit_facts_st();
      cm_call_add_rvalue_temp_facts_st(shape, lvalue_case);
    }
    int count = cm_args_length(expr->args);
    [[cst::proof]] {
      thm length_model = spec_rule(
          `args_:(cm_expr)list`,
          cm_rep_args_length_matches_length);
      substitute_st(length_model);
      substitute_st(assume_rule(
          `retval == ilength (args_:(cm_expr)list)`));
      thm shape = assume_rule(
          `e == CMCallE (callee_:int)
             (args_:(cm_expr)list) (ty_:cm_type)`);
      thm lvalue_case =
          eqt_intro_rule(assume_rule(`lvalue__pre == 0i`));
      thm code_shape = cm_call_code_shape(shape, lvalue_case,
          `cm_emit_args_store (p:cm_program) (fid__pre:int)
             (pc__pre:int) (temp__pre:int)
             (temp__pre + ilength (args_:(cm_expr)list)) args_ ++
           cm_emit_args_reload p fid__pre temp__pre args_ ++
           [TVMInst TVMCallOp
             (cm_function_pc p (callee_:int))]`);
      cm_call_add_initial_store_end_st(code_shape);
      cm_select_code_plan_st(code_shape);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    cm_emit_args_store_plan(program, fid, fn, pc, temp,
        temp + count, temp_limit, expr->args, emitter);
    [[cst::proof]] {
      substitute_st(sym_rule(ispecl_rule(TERM_LIST(
          `cm_emit_args_reload (p:cm_program) (fid__pre:int)
             (temp__pre:int) (args_:(cm_expr)list)`,
          `[TVMInst TVMCallOp
             (cm_function_pc p (callee_:int))]`,
          `tail:(tvm_inst)list`),
          get_theorem_by_name("APPEND_ASSOC"))));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    cm_emit_args_reload_plan(fn, temp, temp_limit,
        expr->args, emitter);
    [[cst::proof]] {
      rewrite_st(THM_LIST(
          get_theorem_by_name("APPEND_ASSOC"),
          get_theorem_by_name("APPEND")));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    cm_emit_call_plan(emitter, expr->value);
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMCallE (callee_:int)
             (args_:(cm_expr)list) (ty_:cm_type)`);
      thm code_shape = cm_call_code_shape(shape,
          eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
          `cm_emit_args_store (p:cm_program) (fid__pre:int)
             (pc__pre:int) (temp__pre:int)
             (temp__pre + ilength (args_:(cm_expr)list)) args_ ++
           cm_emit_args_reload p fid__pre temp__pre args_ ++
           [TVMInst TVMCallOp
             (cm_function_pc p (callee_:int))]`);
      cm_restore_code_plan_end_st(code_shape);
      cm_close_call_payload_st(shape);
    }
  } else {
    [[cst::proof]] {
      thm code_shape = cm_call_code_shape(
          assume_rule(
            `e == CMCallE (callee_:int)
               (args_:(cm_expr)list) (ty_:cm_type)`),
          eqf_intro_rule(assume_rule(`~(lvalue__pre == 0i)`)),
          `[]:(tvm_inst)list`);
      cm_empty_code_plan_end_st(code_shape);
    }
  }
  [[cst::proof]] {
    thm value_model = by_rewrite(
        `cm_rep_expr_value (e:cm_expr) == (callee_:int)`,
        THM_LIST(assume_rule(
          `e == CMCallE (callee_:int)
             (args_:(cm_expr)list) (ty_:cm_type)`),
          get_cm_rep_expr_value_def()));
    substitute_st(sym_rule(value_model));
    cm_close_expr_rep_st();
  }
}
