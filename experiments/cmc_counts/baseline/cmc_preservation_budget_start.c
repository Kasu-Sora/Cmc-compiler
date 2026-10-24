#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "userlib/proof_patterns.h"
#include "cmc_preservation_budget_start.h"
#include "cmc_preservation_budget_defs.h"
#include "cmc_preservation_generation.h"
#include "cmc_preservation_budget_arith.h"
#include "cmc_annotate_erasure.h"

#require "userlib/proof_patterns.c"
#require "cmc_preservation_budget_defs.c"
#require "cmc_preservation_budget_arith.c"
#require "cmc_annotate_erasure.c"

PROOF static size_t _cmc_preservation_budget_start_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_bs_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_bs_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_bs_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static void cm_bs_add_fact_rules(
    thm_list *rules, thm fact) {
  if (is_conj(concl(fact))) {
    cm_bs_add_fact_rules(rules, conjunct1_rule(fact));
    cm_bs_add_fact_rules(rules, conjunct2_rule(fact));
    return;
  }
  vector_add(rules, fact);
}

PROOF static thm_list cm_bs_base_rules(void) {
  return THM_LIST(
      get_cm_step_def(), get_cm_rstart_def(), get_cm_lstart_def(),
      get_cm_sstart_def(), get_cm_begin_call_def(),
      cm_annotation_step_def, cm_update_annotation_def,
      cm_update_r_def, cm_update_l_def, cm_update_s_def,
      cm_ann_plain_def, cm_ann_linear_def, cm_ann_push_def,
      cm_ann_replace_def, cm_ann_pop_def,
      cm_ann_enter_call_def, cm_ann_pc_def, cm_ann_temp_def,
      cm_ann_break_def, cm_ann_continue_def, cm_ann_cursors_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_phase_frame_def, cm_frame_parent_fid_def,
      cm_annotation_erases_def, cm_cursor_frames_def,
      get_cm_task_budget_def(), get_cm_cursors_budget_def(),
      get_cm_phase_budget_def(), get_cm_temp_slots_def(),
      get_cm_stemps_def(), get_cm_ltemps_def(), get_cm_rtemps_def(),
      get_cm_expr_tpair_def(), get_cm_tleft_def(),
      get_cm_tright_def(), get_cm_acount_def(), get_cm_adepth_def(),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("ILENGTH_DEF"),
      get_theorem_by_name("NOT_CONS_NIL"),
      get_datatype_distinctness("cm_expr"),
      get_datatype_injectivity("cm_expr"));
}

PROOF static thm cm_bs_normalize(
    const thm_list rules, thm fact) {
  for (size_t pass = 0; pass < 4; ++pass) {
    fact = conv_rule(reduce_rewrite_conv(rules), fact);
  }
  return fact;
}

PROOF static void cm_bs_close(
    gnode node, const thm_list structural, const thm_list facts) {
  thm_list normalized_facts = (thm_list)vector_create();
  thm_list rules = (thm_list)vector_copy(structural);
  for (size_t i = 0; i < vector_size(facts); ++i) {
    thm normalized = cm_bs_normalize(structural, facts[i]);
    vector_add(&normalized_facts, normalized);
    cm_bs_add_fact_rules(&rules, normalized);
  }
  thm_list branch_rules = (thm_list)vector_copy(structural);
  thm_list normalized_assumptions = (thm_list)vector_create();
  labeled_term_list assumptions = goal_lasmps(node->g);
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    thm normalized = cm_bs_normalize(
        structural, assume_rule(assumptions[i].tm));
    vector_add(&normalized_assumptions, normalized);
    cm_bs_add_fact_rules(&rules, normalized);
    cm_bs_add_fact_rules(&branch_rules, normalized);
  }
  for (size_t pass = 0; pass < 4 && IS_NULL(node->solved); ++pass) {
    node = CONV_WITH_ASMP_TAC(node, reduce_rewrite_conv, rules);
  }
  if (!IS_NULL(node->solved)) return;
  if (is_conj(goal_ccl(node->g))) {
    gnode_list parts = CONJ_TAC(node);
    cm_bs_close(parts[0], structural, facts);
    cm_bs_close(parts[1], structural, facts);
    return;
  }
  thm_list arithmetic = (thm_list)vector_create();
  for (size_t i = 0; i < vector_size(normalized_facts); ++i) {
    vector_add(&arithmetic,
        cm_bs_normalize(branch_rules, normalized_facts[i]));
  }
  for (size_t i = 0;
       i < vector_size(normalized_assumptions); ++i) {
    vector_add(&arithmetic, normalized_assumptions[i]);
  }
  thm joined = list_conj_rule(arithmetic);
  ACCEPT_TAC(node, mp_rule(int_arith_rule(
      mk_imp(concl(joined), goal_ccl(node->g))), joined));
}

PROOF static thm cm_bs_r_budget_open(
    thm shape, const thm_list extra_structural) {
  thm_list rules = THM_LIST(shape, get_cm_task_budget_def());
  for (size_t i = 0; i < vector_size(extra_structural); ++i) {
    vector_add(&rules, extra_structural[i]);
  }
  return conv_rule(reduce_rewrite_conv(rules), assume_rule(
      `cm_task_budget (p:cm_program)
        (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list))
        (ann:cm_annotation)`));
}

PROOF static void cm_bs_r_finish(
    gnode node, thm expression_shape, thm_list extra_structural,
    thm_list extra_facts) {
  thm_list structural = cm_bs_base_rules();
  vector_add(&structural, expression_shape);
  for (size_t i = 0; i < vector_size(extra_structural); ++i) {
    vector_add(&structural, extra_structural[i]);
  }
  thm opened =
      cm_bs_r_budget_open(expression_shape, extra_structural);
  thm_list facts = THM_LIST(opened);
  for (size_t i = 0; i < vector_size(extra_facts); ++i) {
    vector_add(&facts, extra_facts[i]);
  }
  cm_bs_close(node, structural, facts);
}

PROOF static void cm_bs_r_leaf(
    gnode node, thm expression_shape, size_t index,
    thm_list extra_structural) {
  term concrete = rhs_of(expression_shape);
  thm_list structural = cm_bs_base_rules();
  vector_add(&structural, expression_shape);
  for (size_t i = 0; i < vector_size(extra_structural); ++i) {
    vector_add(&structural, extra_structural[i]);
  }
  thm opened =
      cm_bs_r_budget_open(expression_shape, extra_structural);
  thm nonnegative = conjunct1_rule(opened);
  thm bound = conjunct1_rule(conjunct2_rule(opened));
  term base = `cm_ann_temp (ann:cm_annotation)`;
  term limit = `cm_temp_slots
      (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  thm_list facts = THM_LIST(opened, nonnegative, bound);
  if (index == 3) {
    thm parts = specl_rule(TERM_LIST(
        base, limit,
        cm_bs_constructor_arg(concrete, 3, 0),
        cm_bs_constructor_arg(concrete, 3, 1),
        cm_bs_constructor_arg(concrete, 3, 2)),
        cm_r_assign_budget_parts);
    vector_add(&facts, match_mp_rule(parts, bound));
  } else if (index == 4) {
    thm parts = specl_rule(TERM_LIST(
        base, limit,
        cm_bs_constructor_arg(concrete, 4, 0),
        cm_bs_constructor_arg(concrete, 4, 1),
        cm_bs_constructor_arg(concrete, 4, 2),
        cm_bs_constructor_arg(concrete, 4, 3)),
        cm_r_binary_budget_parts);
    vector_add(&facts, match_mp_rule(parts, bound));
  } else if (index == 5 && vector_size(extra_structural) == 0) {
    thm part = specl_rule(TERM_LIST(
        base, limit,
        cm_bs_constructor_arg(concrete, 3, 0),
        cm_bs_constructor_arg(concrete, 3, 1),
        cm_bs_constructor_arg(concrete, 3, 2)),
        cm_r_unary_budget_part);
    vector_add(&facts, match_mp_rule(part, bound));
  } else if (index == 6) {
    thm parts = specl_rule(TERM_LIST(
        base, limit,
        cm_bs_constructor_arg(concrete, 3, 0),
        cm_bs_constructor_arg(concrete, 3, 1),
        cm_bs_constructor_arg(concrete, 3, 2)),
        cm_r_index_budget_parts);
    vector_add(&facts, match_mp_rule(parts, bound));
  } else if (index == 7) {
    thm part = specl_rule(TERM_LIST(
        base, limit,
        cm_bs_constructor_arg(concrete, 3, 0),
        cm_bs_constructor_arg(concrete, 3, 1),
        cm_bs_constructor_arg(concrete, 3, 2)),
        cm_l_member_budget_part);
    thm same_measure = by_rewrite(
        `cm_rtemps
           (CMMemberE
             (${cm_bs_constructor_arg(concrete, 3, 0):cm_expr})
             (${cm_bs_constructor_arg(concrete, 3, 1):int})
             (${cm_bs_constructor_arg(concrete, 3, 2):cm_type})) ==
         cm_ltemps
           (CMMemberE
             (${cm_bs_constructor_arg(concrete, 3, 0):cm_expr})
             (${cm_bs_constructor_arg(concrete, 3, 1):int})
             (${cm_bs_constructor_arg(concrete, 3, 2):cm_type}))`,
        THM_LIST(get_cm_ltemps_def(), get_cm_rtemps_def(),
          get_cm_expr_tpair_def(), get_cm_tleft_def(),
          get_cm_tright_def()));
    vector_add(&facts, match_mp_rule(part, conv_rule(
        rewrite_conv(THM_LIST(same_measure)), bound)));
  }
  cm_bs_close(node, structural, facts);
}

PROOF static thm cm_bs_unary_measure(
    term concrete, bool outer_lvalue, bool inner_lvalue,
    const thm_list conditions) {
  term arg = cm_bs_constructor_arg(concrete, 3, 1);
  term outer = outer_lvalue
      ? `cm_ltemps (${concrete:cm_expr})`
      : `cm_rtemps (${concrete:cm_expr})`;
  term inner = inner_lvalue
      ? `cm_ltemps (${arg:cm_expr})`
      : `cm_rtemps (${arg:cm_expr})`;
  thm_list rules = (thm_list)vector_copy(conditions);
  vector_add(&rules, get_cm_ltemps_def());
  vector_add(&rules, get_cm_rtemps_def());
  vector_add(&rules, get_cm_expr_tpair_def());
  vector_add(&rules, get_cm_tleft_def());
  vector_add(&rules, get_cm_tright_def());
  return by_rewrite(mk_eq(outer, inner), rules);
}
PROOF static void cm_bs_r_cases(gnode node) {

  gnode_list cases = DISJ_CASES_TAC(node,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hbudget_expr");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = cases[i];
    while (is_exists(goal_lasmps(leaf->g)[
        labeled_term_list_index(
          goal_lasmps(leaf->g), "Hbudget_expr")].tm)) {
      leaf = ASMP_EXISTS_TAC(leaf, "Hbudget_expr", NULL);
    }
    thm shape = assume_rule(goal_lasmps(leaf->g)[
        labeled_term_list_index(
          goal_lasmps(leaf->g), "Hbudget_expr")].tm);
    term concrete = rhs_of(shape);
    thm_list extras = THM_LIST();
    if (i == 2) {
      term scope = cm_bs_constructor_arg(concrete, 3, 0);
      term slot = cm_bs_constructor_arg(concrete, 3, 1);
      gnode_list binding_cases = BOOL_CASES_TAC(leaf,
          `cm_binding_array (p:cm_program) (fid:int)
             ${scope:int} ${slot:int}`,
          "Hbudget_binding");
      for (size_t j = 0; j < vector_size(binding_cases); ++j) {
        gnode_list address_cases = BOOL_CASES_TAC(binding_cases[j],
            `cm_binding_address_ok (p:cm_program) (fid:int)
               ${scope:int} ${slot:int} (st:cm_src_state)`,
            "Hbudget_binding_address");
        for (size_t k = 0; k < vector_size(address_cases); ++k) {
          cm_bs_r_leaf(address_cases[k], shape, i, extras);
        }
      }
    } else if (i == 5) {
      term op = cm_bs_constructor_arg(concrete, 3, 0);
      gnode_list deref_cases = BOOL_CASES_TAC(
          leaf, `${op:int} == 2i`, "Hbudget_deref");
      thm deref_measure = cm_bs_unary_measure(
          concrete, false, false,
          THM_LIST(assume_rule(mk_eq(op, `2i`))));
      cm_bs_r_leaf(deref_cases[0], shape, i,
          THM_LIST(deref_measure));
      gnode_list address_cases = BOOL_CASES_TAC(
          deref_cases[1], `${op:int} == 3i`, "Hbudget_address");
      thm address_measure = cm_bs_unary_measure(
          concrete, false, true,
          THM_LIST(
            assume_rule(mk_not(mk_eq(op, `2i`))),
            assume_rule(mk_eq(op, `3i`))));
      cm_bs_r_leaf(address_cases[0], shape, i,
          THM_LIST(address_measure));
      thm ordinary_measure = cm_bs_unary_measure(
          concrete, false, false,
          THM_LIST(
            assume_rule(mk_not(mk_eq(op, `2i`))),
            assume_rule(mk_not(mk_eq(op, `3i`)))));
      cm_bs_r_leaf(address_cases[1], shape, i,
          THM_LIST(ordinary_measure));
    } else if (i == 7) {
      term base = cm_bs_constructor_arg(concrete, 3, 0);
      term mid = cm_bs_constructor_arg(concrete, 3, 1);
      gnode_list member_cases = BOOL_CASES_TAC(leaf,
          `cm_member_array (p:cm_program)
             (cm_expr_type ${base:cm_expr}) ${mid:int}`,
          "Hbudget_member");
      for (size_t j = 0; j < vector_size(member_cases); ++j) {
        cm_bs_r_leaf(member_cases[j], shape, i, extras);
      }
    } else if (i == 8) {
      term callee = cm_bs_constructor_arg(concrete, 3, 0);
      term args = cm_bs_constructor_arg(concrete, 3, 1);
      gnode_list args_cases = BOOL_CASES_TAC(
          leaf, `${args:(cm_expr)list} == []`, "Hbudget_args_nil");
      gnode_list call_cases = BOOL_CASES_TAC(args_cases[0],
          `cm_call_ok (p:cm_program) ${callee:int}
               ([]:(cm_value)list) (st:cm_src_state) &&
             cm_call_depth (ks:(cm_frame)list) < 65536i`,
          "Hbudget_empty_call");
      for (size_t j = 0; j < vector_size(call_cases); ++j) {
        cm_bs_r_leaf(call_cases[j], shape, i, extras);
      }
      gnode_list list_cases = DISJ_CASES_TAC(args_cases[1],
          ispec_rule(args, get_theorem_by_name("list_CASES")),
          "Hbudget_args_shape");
      thm nil_shape = assume_rule(goal_lasmps(list_cases[0]->g)[
          labeled_term_list_index(
            goal_lasmps(list_cases[0]->g),
            "Hbudget_args_shape")].tm);
      CONTR_TAC(list_cases[0], not_elim_rule(
          assume_rule(mk_not(mk_eq(args, `[]:(cm_expr)list`))),
          nil_shape));
      gnode cons = ASMP_EXISTS_TAC(
          list_cases[1], "Hbudget_args_shape", NULL);
      cons = ASMP_EXISTS_TAC(cons, "Hbudget_args_shape", NULL);
      thm list_shape = assume_rule(goal_lasmps(cons->g)[
          labeled_term_list_index(
            goal_lasmps(cons->g), "Hbudget_args_shape")].tm);
      thm_list cons_rules = THM_LIST(list_shape);
      thm_list structural = cm_bs_base_rules();
      vector_add(&structural, shape);
      vector_add(&structural, list_shape);
      thm opened =
          cm_bs_r_budget_open(shape, cons_rules);
      thm bound = conjunct1_rule(conjunct2_rule(opened));
      term cons_args = rhs_of(list_shape);
      term head = cm_bs_constructor_arg(cons_args, 2, 0);
      term rest = cm_bs_constructor_arg(cons_args, 2, 1);
      thm parts = specl_rule(TERM_LIST(
          `cm_ann_temp (ann:cm_annotation)`,
          `cm_temp_slots
             (inth (fid:int)
               (cm_program_functions (p:cm_program)))`,
          callee, head, rest,
          cm_bs_constructor_arg(concrete, 3, 2)),
          cm_r_call_budget_parts);
      parts = match_mp_rule(parts, bound);
      cm_bs_r_finish(cons, shape, cons_rules, THM_LIST(
          parts,
          ispec_rule(rest, get_theorem_by_name("ILENGTH_NONNEG"))));
    } else if (i == 10) {
      gnode_list input_cases = BOOL_CASES_TAC(leaf,
          `cm_state_input (st:cm_src_state) == []`,
          "Hbudget_input_nil");
      cm_bs_r_leaf(input_cases[0], shape, i, extras);
      gnode_list byte_cases = BOOL_CASES_TAC(input_cases[1],
          `tower_byte_value
             (HD (cm_state_input (st:cm_src_state)))`,
          "Hbudget_input_byte");
      for (size_t j = 0; j < vector_size(byte_cases); ++j) {
        cm_bs_r_leaf(byte_cases[j], shape, i, extras);
      }
    } else {
      cm_bs_r_leaf(leaf, shape, i, extras);
    }
  }
}

PROOF static thm cm_prove_task_budget_r_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_annotation_erases (CMRTask p fid expr st ks) ann ==>
         cm_task_budget p (CMRTask p fid expr st ks) ann ==>
         cm_task_budget p
           (cm_step (CMRTask p fid expr st ks))
           (cm_update_annotation
             (cm_annotation_step (CMRTask p fid expr st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  cm_bs_r_cases(leaf);
  return gnode_prove(root);
}
PROOF thm cm_task_budget_r_step =
    cm_prove_task_budget_r_step();

PROOF static thm cm_bs_l_budget_open(
    thm shape, const thm_list extra_structural) {
  thm_list rules = THM_LIST(shape, get_cm_task_budget_def());
  for (size_t i = 0; i < vector_size(extra_structural); ++i) {
    vector_add(&rules, extra_structural[i]);
  }
  return conv_rule(reduce_rewrite_conv(rules), assume_rule(
      `cm_task_budget (p:cm_program)
        (CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list))
        (ann:cm_annotation)`));
}

PROOF static void cm_bs_l_leaf(
    gnode node, thm expression_shape, size_t index,
    thm_list extra_structural) {
  term concrete = rhs_of(expression_shape);
  thm_list structural = cm_bs_base_rules();
  vector_add(&structural, expression_shape);
  for (size_t i = 0; i < vector_size(extra_structural); ++i) {
    vector_add(&structural, extra_structural[i]);
  }
  thm opened =
      cm_bs_l_budget_open(expression_shape, extra_structural);
  thm nonnegative = conjunct1_rule(opened);
  thm bound = conjunct1_rule(conjunct2_rule(opened));
  term base_slot = `cm_ann_temp (ann:cm_annotation)`;
  term limit = `cm_temp_slots
      (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  thm_list facts = THM_LIST(opened, nonnegative, bound);
  if (index == 6) {
    thm parts = specl_rule(TERM_LIST(
        base_slot, limit,
        cm_bs_constructor_arg(concrete, 3, 0),
        cm_bs_constructor_arg(concrete, 3, 1),
        cm_bs_constructor_arg(concrete, 3, 2)),
        cm_l_index_budget_parts);
    vector_add(&facts, match_mp_rule(parts, bound));
  } else if (index == 7) {
    thm part = specl_rule(TERM_LIST(
        base_slot, limit,
        cm_bs_constructor_arg(concrete, 3, 0),
        cm_bs_constructor_arg(concrete, 3, 1),
        cm_bs_constructor_arg(concrete, 3, 2)),
        cm_l_member_budget_part);
    vector_add(&facts, match_mp_rule(part, bound));
  }
  cm_bs_close(node, structural, facts);
}

PROOF static void cm_bs_l_cases(gnode node) {
  gnode_list cases = DISJ_CASES_TAC(node,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hbudget_l_expr");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = cases[i];
    while (is_exists(goal_lasmps(leaf->g)[
        labeled_term_list_index(
          goal_lasmps(leaf->g), "Hbudget_l_expr")].tm)) {
      leaf = ASMP_EXISTS_TAC(leaf, "Hbudget_l_expr", NULL);
    }
    thm shape = assume_rule(goal_lasmps(leaf->g)[
        labeled_term_list_index(
          goal_lasmps(leaf->g), "Hbudget_l_expr")].tm);
    term concrete = rhs_of(shape);
    thm_list extras = THM_LIST();
    if (i == 2) {
      term scope = cm_bs_constructor_arg(concrete, 3, 0);
      term slot = cm_bs_constructor_arg(concrete, 3, 1);
      gnode_list address_cases = BOOL_CASES_TAC(leaf,
          `cm_binding_address_ok (p:cm_program) (fid:int)
             ${scope:int} ${slot:int} (st:cm_src_state)`,
          "Hbudget_l_binding_address");
      for (size_t j = 0; j < vector_size(address_cases); ++j) {
        cm_bs_l_leaf(address_cases[j], shape, i, extras);
      }
    } else if (i == 5) {
      term op = cm_bs_constructor_arg(concrete, 3, 0);
      gnode_list deref_cases = BOOL_CASES_TAC(
          leaf, `${op:int} == 2i`, "Hbudget_l_deref");
      thm deref_measure = cm_bs_unary_measure(
          concrete, true, false,
          THM_LIST(assume_rule(mk_eq(op, `2i`))));
      cm_bs_l_leaf(deref_cases[0], shape, i,
          THM_LIST(deref_measure));
      cm_bs_l_leaf(deref_cases[1], shape, i, extras);
    } else {
      cm_bs_l_leaf(leaf, shape, i, extras);
    }
  }
}

PROOF static thm cm_prove_task_budget_l_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_annotation_erases (CMLTask p fid expr st ks) ann ==>
         cm_task_budget p (CMLTask p fid expr st ks) ann ==>
         cm_task_budget p
           (cm_step (CMLTask p fid expr st ks))
           (cm_update_annotation
             (cm_annotation_step (CMLTask p fid expr st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  cm_bs_l_cases(leaf);
  return gnode_prove(root);
}
PROOF thm cm_task_budget_l_step =
    cm_prove_task_budget_l_step();

PROOF static thm cm_bs_s_budget_open(
    thm shape, const thm_list extra_structural) {
  thm_list rules = THM_LIST(shape, get_cm_task_budget_def());
  for (size_t i = 0; i < vector_size(extra_structural); ++i) {
    vector_add(&rules, extra_structural[i]);
  }
  return conv_rule(reduce_rewrite_conv(rules), assume_rule(
      `cm_task_budget (p:cm_program)
        (CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
          (st:cm_src_state) (ks:(cm_frame)list))
        (ann:cm_annotation)`));
}

PROOF static void cm_bs_s_leaf(
    gnode node, thm statement_shape, size_t index,
    thm_list extra_structural) {
  term concrete = rhs_of(statement_shape);
  thm_list structural = cm_bs_base_rules();
  vector_add(&structural, statement_shape);
  for (size_t i = 0; i < vector_size(extra_structural); ++i) {
    vector_add(&structural, extra_structural[i]);
  }
  thm opened =
      cm_bs_s_budget_open(statement_shape, extra_structural);
  thm nonnegative = conjunct1_rule(opened);
  thm bound = conjunct1_rule(conjunct2_rule(opened));
  term base_slot = `cm_ann_temp (ann:cm_annotation)`;
  term limit = `cm_temp_slots
      (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  thm_list facts = THM_LIST(opened, nonnegative, bound);
  if (index == 4) {
    thm parts = specl_rule(TERM_LIST(
        base_slot, limit,
        cm_bs_constructor_arg(concrete, 2, 0),
        cm_bs_constructor_arg(concrete, 2, 1)),
        cm_s_seq_budget_parts);
    vector_add(&facts, match_mp_rule(parts, bound));
  } else if (index == 6) {
    thm parts = specl_rule(TERM_LIST(
        base_slot, limit,
        cm_bs_constructor_arg(concrete, 3, 0),
        cm_bs_constructor_arg(concrete, 3, 1),
        cm_bs_constructor_arg(concrete, 3, 2)),
        cm_s_if_budget_parts);
    vector_add(&facts, match_mp_rule(parts, bound));
  } else if (index == 7) {
    thm parts = specl_rule(TERM_LIST(
        base_slot, limit,
        cm_bs_constructor_arg(concrete, 2, 0),
        cm_bs_constructor_arg(concrete, 2, 1)),
        cm_s_while_budget_parts);
    vector_add(&facts, match_mp_rule(parts, bound));
  }
  cm_bs_close(node, structural, facts);
}

PROOF static void cm_bs_s_cases(gnode node) {
  gnode_list cases = DISJ_CASES_TAC(node,
      ispec_rule(`stmt:cm_stmt`, get_cm_stmt_cases()), "Hbudget_s_stmt");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = cases[i];
    while (is_exists(goal_lasmps(leaf->g)[
        labeled_term_list_index(
          goal_lasmps(leaf->g), "Hbudget_s_stmt")].tm)) {
      leaf = ASMP_EXISTS_TAC(leaf, "Hbudget_s_stmt", NULL);
    }
    thm shape = assume_rule(goal_lasmps(leaf->g)[
        labeled_term_list_index(
          goal_lasmps(leaf->g), "Hbudget_s_stmt")].tm);
    term concrete = rhs_of(shape);
    thm_list extras = THM_LIST();
    if (i == 2 || i == 3) {
      term slot = cm_bs_constructor_arg(
          concrete, i == 2 ? 1 : 2, 0);
      gnode_list local_cases = BOOL_CASES_TAC(leaf,
          `cm_local_slot_ok (p:cm_program) (fid:int) ${slot:int}`,
          i == 2 ? "Hbudget_decl_slot" : "Hbudget_init_slot");
      for (size_t j = 0; j < vector_size(local_cases); ++j) {
        cm_bs_s_leaf(local_cases[j], shape, i, extras);
      }
    } else {
      cm_bs_s_leaf(leaf, shape, i, extras);
    }
  }
}

PROOF static thm cm_prove_task_budget_s_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (stmt:cm_stmt)
          (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_annotation_erases (CMSTask p fid stmt st ks) ann ==>
         cm_task_budget p (CMSTask p fid stmt st ks) ann ==>
         cm_task_budget p
           (cm_step (CMSTask p fid stmt st ks))
           (cm_update_annotation
             (cm_annotation_step (CMSTask p fid stmt st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  cm_bs_s_cases(leaf);
  return gnode_prove(root);
}
PROOF thm cm_task_budget_s_step =
    cm_prove_task_budget_s_step();

PROOF static int cmc_preservation_budget_start_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_budget_start_axioms_before,
      "cmc_preservation_budget_start introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_budget_start_checks =
    cmc_preservation_budget_start_final_checks();
