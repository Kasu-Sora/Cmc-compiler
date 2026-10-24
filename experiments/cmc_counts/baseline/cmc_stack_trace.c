#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_stack_bound.h"
#require "cmc_stack_bound.c"
#include "cmc_stack_trace.h"

PROOF static size_t _cmc_stack_trace_axioms_before = vector_size(get_all_axioms());

PROOF static thm cm_prove_stack_edges_at_offset(void) {
  gnode root = gnode_new_with_ccl(
      `!(instructions:(tvm_inst)list).
         !(code:(tvm_inst)list) (heights:(int)list)
           (base:int) (annotations:(int)list).
         cm_stack_edges_from code heights base instructions annotations ==>
         !(offset:int).
           0i <= offset ==> offset < ilength instructions ==>
           0i <= inth offset annotations &&
           cm_stack_head_ok code heights (base + offset)
             (inth offset instructions) (inth offset annotations)`);
  gnode_list cases = INDUCT_TAC(root, `instructions:(tvm_inst)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm nonnegative = assume_rule(`0i <= (offset:int)`);
    thm below = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
        assume_rule(`(offset:int) < ilength ([]:(tvm_inst)list)`));
    thm negative = mp_rule(
        int_arith_rule(`(offset:int) < 0i ==> ~(0i <= offset)`), below);
    CONTR_TAC(leaf, contra(negative, nonnegative));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm ih = assume_rule(
        `!(code:(tvm_inst)list) (heights:(int)list)
            (base:int) (annotations:(int)list).
           cm_stack_edges_from code heights base
             (a1:(tvm_inst)list) annotations ==>
           !(offset:int).
             0i <= offset ==> offset < ilength a1 ==>
             0i <= inth offset annotations &&
             cm_stack_head_ok code heights (base + offset)
               (inth offset a1) (inth offset annotations)`);
    term edge_term =
        `cm_stack_edges_from (code:(tvm_inst)list)
           (heights:(int)list) (base:int)
           ((a0:tvm_inst) :: (a1:(tvm_inst)list))
           (annotations:(int)list)`;
    thm edges = cm_matching_assumption(leaf, edge_term);
    thm nonnegative = assume_rule(`0i <= (offset:int)`);
    thm below = assume_rule(
        `(offset:int) <
         ilength ((a0:tvm_inst) :: (a1:(tvm_inst)list))`);
    gnode_list annotation_cases =
        CASES_TAC(leaf, `annotations:(int)list`, "hannotations");
    {
      thm empty = cm_matching_assumption(annotation_cases[0],
          `(annotations:(int)list) == ([]:(int)list)`);
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          empty, get_cm_stack_edges_from_def())), edges);
      CONTR_TAC(annotation_cases[0], impossible);
    }
    {
      gnode branch = annotation_cases[1];
      thm shape = cm_matching_assumption(branch,
          `(annotations:(int)list) ==
           ((a0:int) :: (a1:(int)list))`);
      dest_comb_results annotation_outer = dest_comb(rhs_of(shape));
      dest_comb_results annotation_inner = dest_comb(annotation_outer.tm1);
      term annotation_head = annotation_inner.tm2;
      term annotation_tail = annotation_outer.tm2;
      thm unfolded = pure_rewrite_rule(
          THM_LIST(get_cm_stack_edges_from_def()),
          conv_rule(rewrite_conv(THM_LIST(shape)), edges));
      thm head_nonnegative =
          conjunct1_rule(conjunct2_rule(unfolded));
      thm head_ok =
          conjunct1_rule(conjunct2_rule(conjunct2_rule(unfolded)));
      thm tail_edges = conv_rule(
          reduce_rewrite_conv(THM_LIST(get_theorem_by_name("TL"))),
          conjunct2_rule(conjunct2_rule(conjunct2_rule(unfolded))));
      gnode_list offset_cases =
          BOOL_CASES_TAC(branch, `(offset:int) == 0i`, "hoffset");
      {
        thm heads = conv_rule(reduce_rewrite_conv(THM_LIST(
            get_theorem_by_name("HD"))),
            conj_rule(head_nonnegative, head_ok));
        conv zero_pass = reduce_rewrite_conv(THM_LIST(
            shape, cm_matching_assumption(offset_cases[0],
              `(offset:int) == 0i`),
            get_theorem_by_name("INTH_DEF"),
            get_theorem_by_name("NUM_OF_INT_OF_NUM"),
            get_theorem_by_name("NTH_DEF"),
            get_theorem_by_name("INT_ADD_RID")));
        thm normalized = apply_conversion(
            then_conv(zero_pass, zero_pass),
            goal_ccl(offset_cases[0]->g));
        ACCEPT_TAC(offset_cases[0],
            eq_mp_rule(sym_rule(normalized), heads));
      }
      {
        gnode positive = offset_cases[1];
        thm nonzero = cm_matching_assumption(positive,
            `~((offset:int) == 0i)`);
        thm one = mp_rule(mp_rule(
            int_arith_rule(
              `0i <= (offset:int) ==>
               ~(offset == 0i) ==> 1i <= offset`),
            nonnegative), nonzero);
        thm tail_nonnegative =
            mp_rule(int_arith_rule(
              `1i <= (offset:int) ==> 0i <= offset - 1i`), one);
        thm below_expanded = conv_rule(reduce_rewrite_conv(THM_LIST(
            get_theorem_by_name("ILENGTH_DEF"))), below);
        thm tail_below = mp_rule(
            int_arith_rule(
              `(offset:int) < 1i + ilength (a1:(tvm_inst)list) ==>
               offset - 1i < ilength a1`),
            below_expanded);
        thm tail_instance = specl_rule(
            TERM_LIST(`code:(tvm_inst)list`, `heights:(int)list`,
              `(base:int) + 1i`, annotation_tail), ih);
        thm tail_for_offset = spec_rule(`(offset:int) - 1i`,
            mp_rule(tail_instance, tail_edges));
        thm tail_result = mp_rule(mp_rule(
            tail_for_offset, tail_nonnegative), tail_below);
        thm instruction_index = mp_rule(ispecl_rule(TERM_LIST(
            `a0:tvm_inst`, `a1:(tvm_inst)list`, `offset:int`),
            cm_inth_cons_tail), one);
        thm annotation_index = mp_rule(ispecl_rule(TERM_LIST(
            annotation_head, annotation_tail, `offset:int`),
            cm_inth_cons_tail), one);
        thm annotation_shape_index = beta_norm(ap_term_rule(
            `\xs:(int)list. inth (offset:int) xs`, shape));
        thm annotation_equal =
            trans_rule(annotation_shape_index, annotation_index);
        thm nonnegative_equal = beta_norm(ap_term_rule(
            `\height:int. 0i <= height`, annotation_equal));
        thm desired_nonnegative = eq_mp_rule(
            sym_rule(nonnegative_equal), conjunct1_rule(tail_result));
        thm pc_equal = int_arith_rule(
            `(base:int) + offset ==
             (base + 1i) + (offset - 1i)`);
        thm head_function_equal = beta_norm(ap_term_rule(
            `\pc0:int. \inst:tvm_inst. \height:int.
               cm_stack_head_ok (code:(tvm_inst)list)
                 (heights:(int)list) pc0 inst height`,
            pc_equal));
        thm head_instruction_equal = beta_norm(mk_comb_rule(
            head_function_equal, instruction_index));
        thm head_equal = beta_norm(mk_comb_rule(
            head_instruction_equal, annotation_equal));
        thm desired_head = eq_mp_rule(sym_rule(head_equal),
            conjunct2_rule(tail_result));
        ACCEPT_TAC(positive,
            conj_rule(desired_nonnegative, desired_head));
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_stack_edges_at_offset =
    cm_prove_stack_edges_at_offset();

PROOF static thm cm_prove_stack_edges_at(void) {
  gnode root = gnode_new_with_ccl(
      `!(code:(tvm_inst)list) (heights:(int)list) (pc:int).
         cm_stack_edges_from code heights 0i code heights ==>
         0i <= pc ==> pc < ilength code ==>
         0i <= inth pc heights &&
         cm_stack_head_ok code heights pc
           (inth pc code) (inth pc heights)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm base = specl_rule(TERM_LIST(
      `code:(tvm_inst)list`, `code:(tvm_inst)list`,
      `heights:(int)list`, `0i`, `heights:(int)list`),
      cm_stack_edges_at_offset);
  thm at = spec_rule(`pc:int`, mp_rule(base,
      assume_rule(
        `cm_stack_edges_from (code:(tvm_inst)list)
           (heights:(int)list) 0i code heights`)));
  thm result = mp_rule(mp_rule(at,
      assume_rule(`0i <= (pc:int)`)),
      assume_rule(`(pc:int) < ilength (code:(tvm_inst)list)`));
  ACCEPT_TAC(leaf, conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("INT_ADD_LID"))), result));
  return gnode_prove(root);
}
PROOF thm cm_stack_edges_at = cm_prove_stack_edges_at();

PROOF thm cm_return_sites_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_return_sites (heights:(int)list) ([]:(int)list) = T) &&
     (!returnpc rest.
        cm_return_sites heights
          ((returnpc:int) :: (rest:(int)list)) =
        (inth returnpc heights == 1i &&
         cm_return_sites heights rest))`);
PROOF int _e_cm_return_sites =
    cst_add_const_to_header(`cm_return_sites`);

PROOF thm cm_stack_trace_inv_def = new_rec_definition(
    get_tvm_task_recursion(),
    `(!obj expected input.
        cm_stack_trace_inv (obj:tvm_object) (heights:(int)list)
          (TVMBoot (expected:tvm_object) (input:(int)list)) =
        (expected == obj)) &&
     (!obj heights expected st.
        cm_stack_trace_inv (obj:tvm_object) (heights:(int)list)
          (TVMRunTask (expected:tvm_object) (st:tvm_state)) =
        (expected == obj &&
         cm_return_sites heights (tvm_calls st) &&
         (tvm_target_valid (tvm_object_code obj) (tvm_pc st) ==>
          ilength (tvm_stack st) == inth (tvm_pc st) heights))) &&
     (!obj heights st status kind.
        cm_stack_trace_inv (obj:tvm_object) (heights:(int)list)
          (TVMDoneTask (st:tvm_state) (status:int) (kind:int)) = T)`);
PROOF int _e_cm_stack_trace_inv =
    cst_add_const_to_header(`cm_stack_trace_inv`);

PROOF static thm cm_prove_ilength_tl(void) {
  gnode root = gnode_new_with_ccl(
      `!(xs:(A)list).
         1i <= ilength xs ==>
         ilength (TL xs) == ilength xs - 1i`);
  gnode_list cases = INDUCT_TAC(root, `xs:(A)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
        assume_rule(`1i <= ilength ([]:(A)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("TL"))));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_ilength_tl = cm_prove_ilength_tl();

PROOF static thm cm_prove_ilength_tl_tl(void) {
  gnode root = gnode_new_with_ccl(
      `!(xs:(A)list).
         2i <= ilength xs ==>
         ilength (TL (TL xs)) == ilength xs - 2i`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm depth = assume_rule(`2i <= ilength (xs:(A)list)`);
  thm first = mp_rule(
      spec_rule(`xs:(A)list`, cm_ilength_tl),
      mp_rule(int_arith_rule(
          `2i <= ilength (xs:(A)list) ==>
           1i <= ilength xs`), depth));
  thm tail_depth = mp_rule(mp_rule(int_arith_rule(
      `2i <= ilength (xs:(A)list) ==>
       ilength (TL xs) == ilength xs - 1i ==>
       1i <= ilength (TL xs)`), depth), first);
  thm second = mp_rule(
      spec_rule(`TL (xs:(A)list)`, cm_ilength_tl), tail_depth);
  ACCEPT_TAC(leaf, mp_rule(mp_rule(int_arith_rule(
      `ilength (TL (xs:(A)list)) == ilength xs - 1i ==>
       ilength (TL (TL xs)) == ilength (TL xs) - 1i ==>
       ilength (TL (TL xs)) == ilength xs - 2i`), first), second));
  return gnode_prove(root);
}
PROOF thm cm_ilength_tl_tl = cm_prove_ilength_tl_tl();

PROOF static thm cm_prove_return_sites_pop(void) {
  gnode root = gnode_new_with_ccl(
      `!(calls:(int)list) (heights:(int)list).
         1i <= ilength calls ==>
         cm_return_sites heights calls ==>
         cm_return_sites heights (TL calls) &&
         1i == inth (HD calls) heights`);
  gnode_list cases = INDUCT_TAC(root, `calls:(int)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
        assume_rule(`1i <= ilength ([]:(int)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm sites = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_return_sites_def)),
        assume_rule(
            `cm_return_sites (heights:(int)list)
               ((a0:int) :: (a1:(int)list))`));
    thm result = conj_rule(
        conjunct2_rule(sites), sym_rule(conjunct1_rule(sites)));
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_return_sites_pop = cm_prove_return_sites_pop();

PROOF static term cm_mk_int_le(const term left, const term right) {
  term op = dest_comb(dest_comb(`(x:int) <= (y:int)`).tm1).tm1;
  return mk_comb(mk_comb(op, left), right);
}

PROOF static term cm_mk_int_lt(const term left, const term right) {
  term op = dest_comb(dest_comb(`(x:int) < (y:int)`).tm1).tm1;
  return mk_comb(mk_comb(op, left), right);
}

PROOF static gnode cm_stack_effect_reduce(const gnode leaf) {
  return CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
      get_cm_stack_head_ok_def(), get_cm_stack_at_def(),
      cm_return_sites_def, cm_ilength_tl, cm_ilength_tl_tl,
      get_tvm_inst_op_def(), get_tvm_inst_imm_def(),
      get_tvm_inst_step_def(), get_tvm_action_task_def(),
      get_tvm_next_state_def(), get_tvm_jump_state_def(),
      get_tvm_state_selectors_def(), get_tvm_target_valid_def(),
      get_theorem_by_name("ILENGTH_DEF"),
      get_theorem_by_name("HD"), get_theorem_by_name("TL")));
}

PROOF static gnode cm_stack_effect_add_tail_facts(const gnode leaf) {
  gnode result = leaf;
  labeled_term_list context = goal_lasmps(leaf->g);
  term stack = `tvm_stack (st:tvm_state)`;
  term depth_one =
      cm_mk_int_le(`1i`, `ilength (tvm_stack (st:tvm_state))`);
  term depth_two =
      cm_mk_int_le(`2i`, `ilength (tvm_stack (st:tvm_state))`);
  for (size_t i = 0; i < vector_size(context); ++i) {
    if (alpha_compare(context[i].tm, depth_one) == 0) {
      result = ASSUME_TAC(result, mp_rule(
          ispec_rule(stack, cm_ilength_tl),
          assume_rule(context[i].tm)),
          gc_sprintf("htail_length_%zu", vector_size(context)));
    }
    if (alpha_compare(context[i].tm, depth_two) == 0) {
      result = ASSUME_TAC(result, mp_rule(
          ispec_rule(stack, cm_ilength_tl_tl),
          assume_rule(context[i].tm)),
          gc_sprintf("htail_tail_length_%zu", vector_size(context)));
    }
  }
  term call_depth =
      cm_mk_int_le(`1i`, `ilength (tvm_calls (st:tvm_state))`);
  term return_sites =
      `cm_return_sites (heights:(int)list)
         (tvm_calls (st:tvm_state))`;
  for (size_t i = 0; i < vector_size(context); ++i) {
    if (alpha_compare(context[i].tm, call_depth) != 0) {
      continue;
    }
    for (size_t j = 0; j < vector_size(context); ++j) {
      if (alpha_compare(context[j].tm, return_sites) != 0) {
        continue;
      }
      thm popped = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `tvm_calls (st:tvm_state)`, `heights:(int)list`),
          cm_return_sites_pop), assume_rule(context[i].tm)),
          assume_rule(context[j].tm));
      result = ASSUME_TAC(result, conjunct1_rule(popped),
          gc_sprintf("hreturn_tail_%zu", vector_size(context)));
      result = ASSUME_TAC(result, conjunct2_rule(popped),
          gc_sprintf("hreturn_head_%zu", vector_size(context)));
    }
  }
  return result;
}

PROOF static void cm_stack_effect_split(
    const gnode leaf, const term_list conditions, const size_t index) {
  if (index == vector_size(conditions)) {
    labeled_term_list context = goal_lasmps(leaf->g);
    thm action = assume_rule(context[4].tm);
    thm_list rules = THM_LIST(
        get_cm_stack_head_ok_def(), get_cm_stack_at_def(),
        cm_return_sites_def, cm_ilength_tl, cm_ilength_tl_tl,
        get_tvm_inst_op_def(), get_tvm_inst_imm_def(),
        get_tvm_inst_step_def(), get_tvm_action_task_def(),
        get_tvm_next_state_def(), get_tvm_jump_state_def(),
        get_tvm_state_selectors_def(), get_tvm_target_valid_def(),
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"),
        get_datatype_distinctness("tvm_opcode"),
        get_datatype_distinctness("tvm_task"),
        get_datatype_injectivity("tvm_task"));
    for (size_t i = 5; i < vector_size(context); ++i) {
      thm fact = assume_rule(context[i].tm);
      vector_add(&rules, is_not(context[i].tm)
          ? eqf_intro_rule(fact) : eqt_intro_rule(fact));
    }
    vector_add(&rules, specl_rule(TERM_LIST(
        `inth (tvm_pc (st:tvm_state)) (heights:(int)list)`, `1i`),
        get_theorem_by_name("INT_ADD_SYM")));
    conv pass = reduce_rewrite_conv(rules);
    thm head_shape = conv_rule(
        then_conv(pass, then_conv(pass, pass)),
        assume_rule(context[2].tm));
    thm action_shape = conv_rule(
        then_conv(pass, then_conv(pass, pass)), action);
    if (is_false(concl(action_shape))) {
      CONTR_TAC(leaf, action_shape);
      return;
    }
    action_shape = sym_rule(action_shape);
    gnode headed = ASSUME_TAC(leaf, head_shape, "hheadshape");
    headed = cm_stack_effect_add_tail_facts(headed);
    gnode shaped = ASSUME_TAC(headed, action_shape, "hactionshape");
    gnode reduced = cm_stack_effect_reduce(shaped);
    if (IS_NULL(reduced->solved)) {
      gnode_list decomposed = AUTO_ASMP_DESTRUCT_TAC(reduced);
      for (size_t i = 0; i < vector_size(decomposed); ++i) {
        gnode with_tail =
            cm_stack_effect_add_tail_facts(decomposed[i]);
        gnode final = cm_stack_effect_reduce(with_tail);
        if (IS_NULL(final->solved)) {
          ACCEPT_TAC(final, int_arith_rule(goal_ccl(final->g)));
        }
      }
    }
    return;
  }
  gnode_list cases = BOOL_CASES_TAC(
      leaf, conditions[index], gc_sprintf("hcondition%zu", index));
  for (size_t i = 0; i < vector_size(cases); ++i) {
    cm_stack_effect_split(cases[i], conditions, index + 1);
  }
}

PROOF static thm cm_prove_instruction_stack_effect(void) {
  gnode root = gnode_new_with_ccl(
      `!(op:tvm_opcode) (obj:tvm_object) (code:(tvm_inst)list)
         (heights:(int)list) (imm:int) (st:tvm_state)
         (next:tvm_state).
         0i <= inth (tvm_pc st) heights ==>
         ilength (tvm_stack st) == inth (tvm_pc st) heights ==>
         cm_stack_head_ok code heights (tvm_pc st)
           (TVMInst op imm) (inth (tvm_pc st) heights) ==>
         cm_return_sites heights (tvm_calls st) ==>
         tvm_action_task obj (tvm_inst_step code op imm st) ==
           TVMRunTask obj next ==>
         cm_return_sites heights (tvm_calls next) &&
         (tvm_target_valid code (tvm_pc next) ==>
          ilength (tvm_stack next) ==
            inth (tvm_pc next) heights)`);
  gnode_list cases = INDUCT_TAC(root, `op:tvm_opcode`);
  term stack_length = `ilength (tvm_stack (st:tvm_state))`;
  term stack_head = `HD (tvm_stack (st:tvm_state))`;
  term call_length = `ilength (tvm_calls (st:tvm_state))`;
  term input_empty = `(tvm_input (st:tvm_state)) == []`;
  term target_valid =
      `tvm_target_valid (code:(tvm_inst)list) (imm:int)`;
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    term_list conditions = TERM_LIST();
    if (i == 0) {
      vector_add(&conditions,
          cm_mk_int_lt(stack_length, `65536i`));
    } else if (i == 1 || i == 25 || i == 26) {
      vector_add(&conditions,
          cm_mk_int_le(`1i`, stack_length));
    } else if (i == 2) {
      vector_add(&conditions, mk_conj(
          cm_mk_int_le(`1i`, stack_length),
          cm_mk_int_lt(stack_length, `65536i`)));
    } else if (i == 3) {
      vector_add(&conditions,
          cm_mk_int_le(`2i`, stack_length));
    } else if (i == 4) {
      vector_add(&conditions, mk_conj(
          cm_mk_int_le(`1i`, stack_length),
          mk_comb(`tower_word_valid`, stack_head)));
    } else if (i == 5) {
      vector_add(&conditions, mk_conj(
          cm_mk_int_le(`2i`, stack_length),
          mk_comb(`tower_word_valid`, stack_head)));
    } else if (i == 6) {
      vector_add(&conditions, mk_conj(
          cm_mk_int_le(`1i`, stack_length),
          mk_comb(`tower_addr_valid`, stack_head)));
    } else if (i == 7) {
      vector_add(&conditions, mk_conj(
          cm_mk_int_le(`2i`, stack_length),
          mk_comb(`tower_addr_valid`, stack_head)));
    } else if (i >= 8 && i <= 18) {
      term enough = cm_mk_int_le(`2i`, stack_length);
      if (i == 11 || i == 12) {
        vector_add(&conditions, mk_conj(
            enough, mk_not(mk_eq(stack_head, `0i`))));
      } else {
        vector_add(&conditions, enough);
      }
    } else if (i == 19) {
      vector_add(&conditions, target_valid);
    } else if (i == 20 || i == 21) {
      vector_add(&conditions, cm_mk_int_le(`1i`, stack_length));
      vector_add(&conditions, i == 20
          ? mk_eq(stack_head, `0i`)
          : mk_not(mk_eq(stack_head, `0i`)));
      vector_add(&conditions, target_valid);
    } else if (i == 22) {
      vector_add(&conditions, mk_conj(target_valid,
          cm_mk_int_lt(call_length, `65536i`)));
    } else if (i == 23) {
      vector_add(&conditions, cm_mk_int_le(`1i`, call_length));
    } else if (i == 24) {
      vector_add(&conditions,
          cm_mk_int_lt(stack_length, `65536i`));
      vector_add(&conditions, input_empty);
    } else if (i == 27) {
      vector_add(&conditions, mk_conj(
          cm_mk_int_le(`1i`, stack_length),
          mk_comb(`tower_byte_value`, stack_head)));
    }
    cm_stack_effect_split(leaf, conditions, 0);
  }
  return gnode_prove(root);
}
PROOF thm cm_instruction_stack_effect =
    cm_prove_instruction_stack_effect();


PROOF static thm cm_prove_instruction_trace_effect(void) {
  gnode root = gnode_new_with_ccl(
      `!(act:tvm_action) (op:tvm_opcode) (obj:tvm_object)
         (code:(tvm_inst)list) (heights:(int)list) (imm:int)
         (st:tvm_state).
         0i <= inth (tvm_pc st) heights ==>
         ilength (tvm_stack st) == inth (tvm_pc st) heights ==>
         cm_stack_head_ok code heights (tvm_pc st)
           (TVMInst op imm) (inth (tvm_pc st) heights) ==>
         cm_return_sites heights (tvm_calls st) ==>
         code == tvm_object_code obj ==>
         tvm_inst_step code op imm st == act ==>
         cm_stack_trace_inv obj heights (tvm_action_task obj act)`);
  gnode_list cases = INDUCT_TAC(root, `act:tvm_action`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm nonnegative = assume_rule(
        `0i <= inth (tvm_pc (st:tvm_state)) (heights:(int)list)`);
    thm stack = assume_rule(
        `ilength (tvm_stack (st:tvm_state)) ==
         inth (tvm_pc st) (heights:(int)list)`);
    thm head = assume_rule(
        `cm_stack_head_ok (code:(tvm_inst)list) (heights:(int)list)
           (tvm_pc (st:tvm_state)) (TVMInst (op:tvm_opcode) (imm:int))
           (inth (tvm_pc st) heights)`);
    thm returns = assume_rule(
        `cm_return_sites (heights:(int)list) (tvm_calls (st:tvm_state))`);
    thm code_eq = assume_rule(
        `(code:(tvm_inst)list) == tvm_object_code (obj:tvm_object)`);
    thm action_eq = assume_rule(
        `tvm_inst_step (code:(tvm_inst)list) (op:tvm_opcode) (imm:int)
           (st:tvm_state) == TVMStepState (a:tvm_state)`);
    thm run_eq = by_rewrite(
        `tvm_action_task (obj:tvm_object)
           (tvm_inst_step (code:(tvm_inst)list) (op:tvm_opcode)
             (imm:int) (st:tvm_state)) ==
         TVMRunTask obj (a:tvm_state)`,
        THM_LIST(action_eq, get_tvm_action_task_def()));
    thm effect = mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(
        specl_rule(TERM_LIST(
            `op:tvm_opcode`, `obj:tvm_object`, `code:(tvm_inst)list`,
            `heights:(int)list`, `imm:int`, `st:tvm_state`,
            `a:tvm_state`), cm_instruction_stack_effect),
        nonnegative), stack), head), returns), run_eq);
    effect = conv_rule(rewrite_conv(THM_LIST(code_eq)), effect);
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_tvm_action_task_def(), cm_stack_trace_inv_def, code_eq)));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, effect);
    }
  }
  for (size_t i = 1; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_tvm_action_task_def(), cm_stack_trace_inv_def)));
  }
  return gnode_prove(root);
}
PROOF thm cm_instruction_trace_effect =
    cm_prove_instruction_trace_effect();

PROOF static thm cm_prove_stack_trace_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(obj:tvm_object) (heights:(int)list)
         (entries:(int)list) (arities:(int)list) (peak:int)
         (task:tvm_task).
         cm_stack_certificate obj heights entries arities peak ==>
         cm_stack_trace_inv obj heights task ==>
         cm_stack_trace_inv obj heights (tvm_step task)`);
  gnode_list cases = INDUCT_TAC(root, `task:tvm_task`);
  {
    gnode boot = AUTO_INTROS_TAC(cases[0]);
    thm certificate = assume_rule(
        `cm_stack_certificate (obj:tvm_object) (heights:(int)list)
           (entries:(int)list) (arities:(int)list) (peak:int)`);
    thm invariant = assume_rule(
        `cm_stack_trace_inv (obj:tvm_object) (heights:(int)list)
           (TVMBoot (a0:tvm_object) (a1:(int)list))`);
    thm certificate_shape = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_stack_certificate_def())), certificate);
    thm object_eq = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_stack_trace_inv_def)), invariant);
    thm object_wf = conjunct1_rule(certificate_shape);
    thm wf_shape = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_tvm_object_wf_def())), object_wf);
    thm load_obj = conjunct1_rule(wf_shape);
    thm load_expected = conv_rule(
        rewrite_conv(THM_LIST(sym_rule(object_eq))), load_obj);
    thm entry_height = conjunct1_rule(conjunct2_rule(
        conjunct2_rule(certificate_shape)));
    CONV_TAC(boot, reduce_rewrite_conv(THM_LIST(
        get_tvm_step_def(), load_expected, cm_stack_trace_inv_def,
        get_tvm_initial_state_def(), get_tvm_state_selectors_def(),
        cm_return_sites_def, object_eq, entry_height,
        get_theorem_by_name("ILENGTH_DEF"))));
  }
  {
    gnode run = AUTO_INTROS_TAC(cases[1]);
    thm certificate = assume_rule(
        `cm_stack_certificate (obj:tvm_object) (heights:(int)list)
           (entries:(int)list) (arities:(int)list) (peak:int)`);
    thm invariant = assume_rule(
        `cm_stack_trace_inv (obj:tvm_object) (heights:(int)list)
           (TVMRunTask (a0:tvm_object) (a1:tvm_state))`);
    thm certificate_shape = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_stack_certificate_def())), certificate);
    thm invariant_shape = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_stack_trace_inv_def)), invariant);
    thm object_eq = conjunct1_rule(invariant_shape);
    thm returns = conjunct1_rule(conjunct2_rule(invariant_shape));
    thm stack_at_pc = conjunct2_rule(conjunct2_rule(invariant_shape));
    thm edges = conjunct1_rule(conjunct2_rule(conjunct2_rule(
        conjunct2_rule(certificate_shape))));
    term valid_term =
        `tvm_target_valid (tvm_object_code (a0:tvm_object))
           (tvm_pc (a1:tvm_state))`;
    gnode_list valid_cases =
        BOOL_CASES_TAC(run, valid_term, "hcurrent_valid");
    for (size_t i = 0; i < vector_size(valid_cases); ++i) {
      gnode branch = valid_cases[i];
      labeled_term_list context = goal_lasmps(branch->g);
      thm decision = assume_rule(
          context[vector_size(context) - 1].tm);
      if (is_not(concl(decision))) {
        CONV_TAC(branch, reduce_rewrite_conv(THM_LIST(
            get_tvm_step_def(), cm_stack_trace_inv_def, decision)));
        continue;
      }
      thm valid_obj = conv_rule(
          rewrite_conv(THM_LIST(object_eq)), decision);
      thm valid_shape = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_tvm_target_valid_def())), valid_obj);
      thm pc_nonnegative = conjunct1_rule(valid_shape);
      thm pc_bounded = conjunct2_rule(valid_shape);
      term code = `tvm_object_code (obj:tvm_object)`;
      term pc = `tvm_pc (a1:tvm_state)`;
      term inst = `inth (tvm_pc (a1:tvm_state))
          (tvm_object_code (obj:tvm_object))`;
      term op = `tvm_inst_op
          (inth (tvm_pc (a1:tvm_state))
            (tvm_object_code (obj:tvm_object)))`;
      term imm = `tvm_inst_imm
          (inth (tvm_pc (a1:tvm_state))
            (tvm_object_code (obj:tvm_object)))`;
      term action = mk_comb(mk_comb(mk_comb(mk_comb(
          `tvm_inst_step`, code), op), imm), `a1:tvm_state`);
      thm at = mp_rule(mp_rule(mp_rule(
          specl_rule(TERM_LIST(
              code, `heights:(int)list`, pc), cm_stack_edges_at),
          edges), pc_nonnegative), pc_bounded);
      thm current_height = mp_rule(stack_at_pc, valid_obj);
      thm reconstruct =
          spec_rule(inst, get_tvm_inst_reconstruct());
      thm trace = specl_rule(TERM_LIST(
          action, op, `obj:tvm_object`, code, `heights:(int)list`,
          imm, `a1:tvm_state`), cm_instruction_trace_effect);
      trace = conv_rule(
          once_rewrite_conv(THM_LIST(reconstruct)), trace);
      trace = mp_rule(trace, conjunct1_rule(at));
      trace = mp_rule(trace, current_height);
      trace = mp_rule(trace, conjunct2_rule(at));
      trace = mp_rule(trace, returns);
      thm preserved = mp_rule(trace, refl_rule(action));
      gnode reduced = CONV_TAC(branch, reduce_rewrite_conv(THM_LIST(
          get_tvm_step_def(), decision, object_eq)));
      if (IS_NULL(reduced->solved)) {
        ACCEPT_TAC(reduced, preserved);
      }
    }
  }
  {
    gnode done = AUTO_INTROS_TAC(cases[2]);
    CONV_TAC(done, reduce_rewrite_conv(THM_LIST(
        get_tvm_step_def(), cm_stack_trace_inv_def)));
  }
  return gnode_prove(root);
}
PROOF thm cm_stack_trace_step = cm_prove_stack_trace_step();


PROOF static thm cm_prove_stack_trace_iter(void) {
  gnode root = gnode_new_with_ccl(
      `!(n:num). !(obj:tvm_object) (heights:(int)list)
         (entries:(int)list) (arities:(int)list) (peak:int)
         (task:tvm_task).
         cm_stack_certificate obj heights entries arities peak ==>
         cm_stack_trace_inv obj heights task ==>
         cm_stack_trace_inv obj heights (tvm_iter n task)`);
  gnode_list cases = INDUCT_TAC(root, `n:num`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        get_tvm_iter_def()));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm certificate = assume_rule(
        `cm_stack_certificate (obj:tvm_object) (heights:(int)list)
           (entries:(int)list) (arities:(int)list) (peak:int)`);
    thm invariant = assume_rule(
        `cm_stack_trace_inv (obj:tvm_object) (heights:(int)list)
           (task:tvm_task)`);
    thm step = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `obj:tvm_object`, `heights:(int)list`, `entries:(int)list`,
        `arities:(int)list`, `peak:int`, `task:tvm_task`),
        cm_stack_trace_step), certificate), invariant);
    thm ih = assume_rule(
        `!(obj:tvm_object) (heights:(int)list)
           (entries:(int)list) (arities:(int)list) (peak:int)
           (task:tvm_task).
           cm_stack_certificate obj heights entries arities peak ==>
           cm_stack_trace_inv obj heights task ==>
           cm_stack_trace_inv obj heights
             (tvm_iter (n:num) task)`);
    thm result = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `obj:tvm_object`, `heights:(int)list`, `entries:(int)list`,
        `arities:(int)list`, `peak:int`, `tvm_step (task:tvm_task)`),
        ih), certificate), step);
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_tvm_iter_def())));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_stack_trace_iter = cm_prove_stack_trace_iter();

PROOF static thm cm_prove_direct_stack_trace_reachable(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list) (n:num).
         cm_wf_program p ==>
         cm_stack_trace_inv
           (cm_compile_model p)
           (cm_codegen_direct_heights p)
           (tvm_iter n (TVMBoot (cm_compile_model p) input))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm certificate = mp_rule(spec_rule(
      `p:cm_program`, cm_direct_stack_certificate), wf);
  thm initial = by_rewrite(
      `cm_stack_trace_inv
         (cm_compile_model (p:cm_program))
         (cm_codegen_direct_heights p)
         (TVMBoot (cm_compile_model p) (input:(int)list))`,
      THM_LIST(cm_stack_trace_inv_def));
  thm result = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `n:num`, `cm_compile_model (p:cm_program)`,
      `cm_codegen_direct_heights (p:cm_program)`,
      `cm_codegen_function_entries (p:cm_program)`,
      `cm_codegen_function_arities (p:cm_program)`,
      `cm_stack_height_max (cm_codegen_direct_heights p)`,
      `TVMBoot (cm_compile_model p) (input:(int)list)`),
      cm_stack_trace_iter), certificate), initial);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_direct_stack_trace_reachable =
    cm_prove_direct_stack_trace_reachable();

PROOF static thm cm_prove_heights_le_at(void) {
  gnode root = gnode_new_with_ccl(
      `!(heights:(int)list). !(bound:int) (pc:int).
         cm_heights_le bound heights ==>
         0i <= pc ==> pc < ilength heights ==>
         inth pc heights <= bound`);
  gnode_list cases = INDUCT_TAC(root, `heights:(int)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm nonnegative = assume_rule(`0i <= (pc:int)`);
    thm below = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
        assume_rule(`(pc:int) < ilength ([]:(int)list)`));
    thm negative = mp_rule(
        int_arith_rule(`(pc:int) < 0i ==> ~(0i <= pc)`), below);
    CONTR_TAC(leaf, contra(negative, nonnegative));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm ih = assume_rule(
        `!(bound:int) (pc:int).
           cm_heights_le bound (a1:(int)list) ==>
           0i <= pc ==> pc < ilength a1 ==>
           inth pc a1 <= bound`);
    thm bounded = assume_rule(
        `cm_heights_le (bound:int)
           ((a0:int) :: (a1:(int)list))`);
    thm parts = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_heights_le_def)), bounded);
    thm nonnegative = assume_rule(`0i <= (pc:int)`);
    thm below = assume_rule(
        `(pc:int) < ilength ((a0:int) :: (a1:(int)list))`);
    gnode_list pc_cases =
        BOOL_CASES_TAC(leaf, `(pc:int) == 0i`, "hpc_zero");
    {
      thm zero = assume_rule(`(pc:int) == 0i`);
      gnode reduced = CONV_TAC(pc_cases[0],
          reduce_rewrite_conv(THM_LIST(
              zero, get_theorem_by_name("INTH_DEF"),
              get_theorem_by_name("NUM_OF_INT_OF_NUM"),
              get_theorem_by_name("NTH_DEF"))));
      if (IS_NULL(reduced->solved)) {
        ACCEPT_TAC(reduced, conjunct1_rule(parts));
      }
    }
    {
      thm nonzero = assume_rule(`~((pc:int) == 0i)`);
      thm one = mp_rule(mp_rule(int_arith_rule(
          `0i <= (pc:int) ==> ~(pc == 0i) ==> 1i <= pc`),
          nonnegative), nonzero);
      thm tail_nonnegative = mp_rule(int_arith_rule(
          `1i <= (pc:int) ==> 0i <= pc - 1i`), one);
      thm below_expanded = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))), below);
      thm tail_below = mp_rule(int_arith_rule(
          `(pc:int) < 1i + ilength (a1:(int)list) ==>
           pc - 1i < ilength a1`), below_expanded);
      thm tail_result = mp_rule(mp_rule(mp_rule(
          specl_rule(TERM_LIST(`bound:int`, `(pc:int) - 1i`), ih),
          conjunct2_rule(parts)), tail_nonnegative), tail_below);
      thm index = mp_rule(ispecl_rule(TERM_LIST(
          `a0:int`, `a1:(int)list`, `pc:int`),
          cm_inth_cons_tail), one);
      thm indexed_bound = eq_mp_rule(
          beta_norm(ap_term_rule(
              `\height0:int. height0 <= (bound:int)`, sym_rule(index))),
          tail_result);
      ACCEPT_TAC(pc_cases[1], indexed_bound);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_heights_le_at = cm_prove_heights_le_at();

PROOF static thm cm_prove_stack_bound(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list) (n:num) (st:tvm_state).
         cm_wf_program p ==>
         tvm_iter n (TVMBoot (cm_compile_model p) input) ==
           TVMRunTask (cm_compile_model p) st ==>
         tvm_target_valid
           (tvm_object_code (cm_compile_model p)) (tvm_pc st) ==>
         ilength (tvm_stack st) <= cm_stack_bound_model p &&
         cm_stack_bound_model p <= 65536i`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm reached = assume_rule(
      `tvm_iter (n:num)
         (TVMBoot (cm_compile_model (p:cm_program)) (input:(int)list)) ==
       TVMRunTask (cm_compile_model p) (st:tvm_state)`);
  thm valid = assume_rule(
      `tvm_target_valid
         (tvm_object_code (cm_compile_model (p:cm_program)))
         (tvm_pc (st:tvm_state))`);
  thm invariant = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`, `n:num`),
      cm_direct_stack_trace_reachable), wf);
  invariant = conv_rule(rewrite_conv(THM_LIST(reached)), invariant);
  thm invariant_shape = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_stack_trace_inv_def)), invariant);
  thm stack_at_pc = cm_pick_conjunct(invariant_shape,
      `tvm_target_valid
         (tvm_object_code (cm_compile_model (p:cm_program)))
         (tvm_pc (st:tvm_state)) ==>
       ilength (tvm_stack st) ==
         inth (tvm_pc st) (cm_codegen_direct_heights p)`);
  thm current_height = mp_rule(stack_at_pc, valid);
  thm valid_shape = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_tvm_target_valid_def())), valid);
  thm certificate = mp_rule(spec_rule(
      `p:cm_program`, cm_direct_stack_certificate), wf);
  thm certificate_shape = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_stack_certificate_def())), certificate);
  thm length = cm_pick_conjunct(certificate_shape,
      `ilength (cm_codegen_direct_heights (p:cm_program)) ==
       ilength (tvm_object_code (cm_compile_model p))`);
  thm pc_bounded = conv_rule(
      rewrite_conv(THM_LIST(sym_rule(length))),
      conjunct2_rule(valid_shape));
  thm heights_bounded = mp_rule(spec_rule(
      `p:cm_program`, cm_direct_codegen_bounded), wf);
  thm annotation_bound = mp_rule(mp_rule(mp_rule(
      specl_rule(TERM_LIST(
          `cm_codegen_direct_heights (p:cm_program)`,
          `cm_stack_bound_model (p:cm_program)`,
          `tvm_pc (st:tvm_state)`), cm_heights_le_at),
      heights_bounded), conjunct1_rule(valid_shape)), pc_bounded);
  thm stack_bound = conv_rule(
      rewrite_conv(THM_LIST(sym_rule(current_height))),
      annotation_bound);
  thm wf_shape = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_wf_program_def(), get_cm_codegen_admissible_def())), wf);
  thm machine_bound = cm_pick_conjunct(wf_shape,
      `cm_stack_bound_model (p:cm_program) <= 65536i`);
  ACCEPT_TAC(leaf, conj_rule(stack_bound, machine_bound));
  return gnode_prove(root);
}
PROOF thm cmc_stack_bound = cm_prove_stack_bound();
PROOF thm get_cmc_stack_discipline(void) {
  return cmc_stack_discipline;
}

PROOF thm get_cmc_stack_bound(void) {
  return cmc_stack_bound;
}

PROOF static int cmc_stack_trace_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_stack_trace_axioms_before,
      "cmc_stack_trace introduced an axiom");
  ENSURE_COND(!IS_NULL(get_cmc_stack_discipline()) &&
      vector_size(hyp(get_cmc_stack_discipline())) == 0 &&
      vector_size(free_vars(concl(get_cmc_stack_discipline()))) == 0 &&
      alpha_compare(concl(get_cmc_stack_discipline()),
        `!(p:cm_program).
           cm_wf_program p ==>
           cm_stack_summary
             (cm_compile_model p)
             (cm_stack_bound_model p)`) == 0,
      "compiler stack-discipline theorem has the wrong contract");
  ENSURE_COND(!IS_NULL(get_cmc_stack_bound()) &&
      vector_size(hyp(get_cmc_stack_bound())) == 0 &&
      vector_size(free_vars(concl(get_cmc_stack_bound()))) == 0 &&
      alpha_compare(concl(get_cmc_stack_bound()),
        `!(p:cm_program) (input:(int)list) (n:num) (st:tvm_state).
           cm_wf_program p ==>
           tvm_iter n (TVMBoot (cm_compile_model p) input) ==
             TVMRunTask (cm_compile_model p) st ==>
           tvm_target_valid
             (tvm_object_code (cm_compile_model p)) (tvm_pc st) ==>
           ilength (tvm_stack st) <= cm_stack_bound_model p &&
           cm_stack_bound_model p <= 65536i`) == 0,
      "compiler reachable stack-bound theorem has the wrong contract");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_stack_trace_checks =
    cmc_stack_trace_final_checks();
