#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "userlib/proof_patterns.h"
#include "cmc_preservation_budget_value.h"
#include "cmc_preservation_budget_defs.h"
#include "cmc_preservation_budget_arith.h"
#include "cmc_preservation_ready_coordinate.h"
#include "cmc_preservation_generation.h"
#include "cmc_preservation_type_ready.h"

#require "userlib/proof_patterns.c"
#require "cmc_preservation_budget_defs.c"
#require "cmc_preservation_budget_arith.c"
#require "cmc_preservation_ready_coordinate.c"
#require "cmc_preservation_type_ready.c"

PROOF static size_t _cmc_preservation_budget_value_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_bv_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_bv_constructor_arg(
    term tm, size_t arity, size_t index) {
  return cm_bv_app_arg_from_right(tm, arity - index - 1);
}

PROOF static void cm_bv_add_fact_rules(thm_list *rules, thm fact) {
  if (is_conj(concl(fact))) {
    cm_bv_add_fact_rules(rules, conjunct1_rule(fact));
    cm_bv_add_fact_rules(rules, conjunct2_rule(fact));
    return;
  }
  vector_add(rules, fact);
}

PROOF static thm cm_bv_normalize(
    const thm_list rules, thm fact) {
  for (size_t pass = 0; pass < 5; ++pass) {
    fact = conv_rule(reduce_rewrite_conv(rules), fact);
  }
  return fact;
}

PROOF static thm_list cm_bv_base_rules(void) {
  return THM_LIST(
      get_cm_step_def(), get_cm_vapply_def(), get_cm_begin_call_def(),
      cm_annotation_step_def, cm_update_annotation_def, cm_update_v_def,
      cm_ann_plain_def, cm_ann_linear_def, cm_ann_push_def,
      cm_ann_replace_def, cm_ann_pop_def, cm_ann_enter_call_def,
      cm_ann_spills_set_def, cm_ann_put_spill_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_cursor_break_def, cm_cursor_continue_def,
      cm_annotation_erases_def, cm_cursor_frames_def,
      cm_phase_frame_def, cm_frame_parent_fid_def,
      get_cm_task_budget_def(), get_cm_cursors_budget_def(),
      get_cm_phase_budget_def(), get_cm_temp_slots_def(),
      cm_task_coordinate_ready_def, cm_annotation_child_ready_def,
      cm_cursors_coordinate_def, cm_phase_child_temp_def,
      cm_phase_next_fid_def,
      get_cm_task_type_ready_def(),
      get_cm_cursor_head_value_type_ready_def(),
      get_cm_phase_value_type_ready_def(),
      get_cm_stemps_def(), get_cm_rtemps_def(),
      get_cm_acount_def(), get_cm_adepth_def(),
      get_cm_args_temps_def(),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("ILENGTH_DEF"),
      get_theorem_by_name("COND_ID"),
      get_theorem_by_name("NOT_CONS_NIL"),
      get_datatype_distinctness("cm_frame"),
      get_datatype_injectivity("cm_frame"));
}

PROOF static void cm_bv_close(
    gnode node, const thm_list structural,
    const thm_list supplied_facts) {
  thm_list normalized_facts = (thm_list)vector_create();
  thm_list rules = (thm_list)vector_copy(structural);
  for (size_t i = 0; i < vector_size(supplied_facts); ++i) {
    thm normalized = cm_bv_normalize(structural, supplied_facts[i]);
    vector_add(&normalized_facts, normalized);
    cm_bv_add_fact_rules(&rules, normalized);
  }
  thm_list branch_rules = (thm_list)vector_copy(structural);
  thm_list normalized_assumptions = (thm_list)vector_create();
  labeled_term_list assumptions = goal_lasmps(node->g);
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    thm normalized = cm_bv_normalize(
        structural, assume_rule(assumptions[i].tm));
    vector_add(&normalized_assumptions, normalized);
    cm_bv_add_fact_rules(&rules, normalized);
    cm_bv_add_fact_rules(&branch_rules, normalized);
  }
  for (size_t pass = 0; pass < 5 && IS_NULL(node->solved); ++pass) {
    node = CONV_WITH_ASMP_TAC(node, reduce_rewrite_conv, rules);
  }
  if (!IS_NULL(node->solved)) return;
  if (is_conj(goal_ccl(node->g))) {
    gnode_list parts = CONJ_TAC(node);
    cm_bv_close(parts[0], structural, supplied_facts);
    cm_bv_close(parts[1], structural, supplied_facts);
    return;
  }
  thm_list arithmetic = (thm_list)vector_create();
  for (size_t i = 0; i < vector_size(normalized_facts); ++i) {
    vector_add(&arithmetic,
        cm_bv_normalize(branch_rules, normalized_facts[i]));
  }
  for (size_t i = 0;
       i < vector_size(normalized_assumptions); ++i) {
    vector_add(&arithmetic, normalized_assumptions[i]);
  }
  thm joined = list_conj_rule(arithmetic);
  ACCEPT_TAC(node, mp_rule(int_arith_rule(
      mk_imp(concl(joined), goal_ccl(node->g))), joined));
}

PROOF static thm cm_bv_assumption(const char *label, gnode node) {
  labeled_term_list assumptions = goal_lasmps(node->g);
  return assume_rule(assumptions[
      labeled_term_list_index(assumptions, label)].tm);
}

PROOF static void cm_bv_phase_leaf(
    gnode node, thm cursors_shape, thm phase_shape,
    thm frames_shape, const thm_list extra_structural,
    const thm_list extra_facts) {
  thm_list structural = cm_bv_base_rules();
  vector_add(&structural, cursors_shape);
  vector_add(&structural, phase_shape);
  vector_add(&structural, frames_shape);
  for (size_t i = 0; i < vector_size(extra_structural); ++i) {
    vector_add(&structural, extra_structural[i]);
  }
  thm_list facts = THM_LIST(
      assume_rule(`cm_task_type_ready (p:cm_program)
        (CMVTask p (fid:int) (v:cm_value) (st:cm_src_state)
          (ks:(cm_frame)list)) (ann:cm_annotation)`),
      assume_rule(`cm_task_coordinate_ready (p:cm_program)
        (CMVTask p (fid:int) (v:cm_value) (st:cm_src_state)
          (ks:(cm_frame)list)) (ann:cm_annotation)`),
      assume_rule(`cm_task_budget (p:cm_program)
        (CMVTask p (fid:int) (v:cm_value) (st:cm_src_state)
          (ks:(cm_frame)list)) (ann:cm_annotation)`));
  for (size_t i = 0; i < vector_size(extra_facts); ++i) {
    vector_add(&facts, extra_facts[i]);
  }
  cm_bv_close(node, structural, facts);
}

PROOF static thm cm_bv_arg_parts(
    thm cursors_shape, thm phase_shape, thm rest_shape) {
  term concrete_phase = rhs_of(phase_shape);
  term rest = cm_bv_constructor_arg(concrete_phase, 8, 1);
  term current_slot = cm_bv_constructor_arg(concrete_phase, 8, 6);
  term scratch = cm_bv_constructor_arg(concrete_phase, 8, 7);
  term concrete_rest = rhs_of(rest_shape);
  term arg = cm_bv_constructor_arg(concrete_rest, 2, 0);
  term tail = cm_bv_constructor_arg(concrete_rest, 2, 1);
  term limit = `cm_temp_slots
      (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  thm_list rules = THM_LIST(
      cursors_shape, phase_shape, rest_shape,
      get_cm_task_budget_def(), get_cm_cursors_budget_def(),
      get_cm_phase_budget_def(), cm_ann_cursors_def,
      cm_cursor_phase_def, cm_cursor_temp_def);
  thm opened = cm_bv_normalize(rules, assume_rule(
      `cm_task_budget (p:cm_program)
        (CMVTask p (fid:int) (v:cm_value) (st:cm_src_state)
          (ks:(cm_frame)list)) (ann:cm_annotation)`));
  thm cursor_step = find_conjunct_rule(opened,
      `${current_slot:int} + 1i + ilength (${arg:cm_expr} ::
          ${tail:(cm_expr)list}) == ${scratch:int}`);
  thm tail_bound = find_conjunct_rule(opened,
      `${scratch:int} + cm_adepth
          (cm_args_apair (${arg:cm_expr} :: ${tail:(cm_expr)list})) <=
        ${limit:int}`);
  thm result = specl_rule(TERM_LIST(
      current_slot, scratch, limit, arg, tail),
      cm_arg_budget_tail_parts);
  result = match_mp_rule(result, cursor_step);
  return match_mp_rule(result, tail_bound);
}

PROOF static void cm_bv_split_phase(
    gnode node, thm cursors_shape, thm frames_shape,
    term head_cursor, term cursor_tail) {
  term phase = `cm_cursor_phase (${head_cursor:cm_acursor})`;
  gnode_list phase_cases = DISJ_CASES_TAC(node,
      ispec_rule(phase, get_datatype_cases("cm_aphase")),
      "Hbudget_v_phase");
  for (size_t i = 0; i < vector_size(phase_cases); ++i) {
    gnode branch = phase_cases[i];
    while (is_exists(concl(cm_bv_assumption("Hbudget_v_phase", branch)))) {
      branch = ASMP_EXISTS_TAC(branch, "Hbudget_v_phase", NULL);
    }
    thm phase_shape = cm_bv_assumption("Hbudget_v_phase", branch);
    term concrete_phase = rhs_of(phase_shape);
    thm_list none = THM_LIST();
    if (i == 1) {
      term ty = cm_bv_constructor_arg(concrete_phase, 1, 0);
      gnode_list load_cases = BOOL_CASES_TAC(branch,
          `cm_load_ok ${ty:cm_type} (v:cm_value)
             (st:cm_src_state)`,
          "Hbudget_v_load");
      for (size_t j = 0; j < vector_size(load_cases); ++j) {
        cm_bv_phase_leaf(load_cases[j], cursors_shape, phase_shape,
            frames_shape, none, none);
      }
    } else if (i == 3) {
      term pointer = cm_bv_constructor_arg(concrete_phase, 2, 0);
      term ty = cm_bv_constructor_arg(concrete_phase, 2, 1);
      gnode_list store_cases = BOOL_CASES_TAC(branch,
          `cm_store_ok ${ty:cm_type} ${pointer:cm_value}
             (st:cm_src_state)`,
          "Hbudget_v_store");
      for (size_t j = 0; j < vector_size(store_cases); ++j) {
        cm_bv_phase_leaf(store_cases[j], cursors_shape, phase_shape,
            frames_shape, none, none);
      }
    } else if (i == 4) {
      term op = cm_bv_constructor_arg(concrete_phase, 4, 0);
      gnode_list or_cases = BOOL_CASES_TAC(
          branch, `${op:int} == 0i`, "Hbudget_v_or");
      gnode_list or_truth = BOOL_CASES_TAC(or_cases[0],
          `cm_truth (st:cm_src_state) (v:cm_value)`,
          "Hbudget_v_or_truth");
      for (size_t j = 0; j < vector_size(or_truth); ++j) {
        cm_bv_phase_leaf(or_truth[j], cursors_shape, phase_shape,
            frames_shape, none, none);
      }
      gnode_list and_cases = BOOL_CASES_TAC(
          or_cases[1], `${op:int} == 1i`, "Hbudget_v_and");
      gnode_list and_truth = BOOL_CASES_TAC(and_cases[0],
          `cm_truth (st:cm_src_state) (v:cm_value)`,
          "Hbudget_v_and_truth");
      for (size_t j = 0; j < vector_size(and_truth); ++j) {
        cm_bv_phase_leaf(and_truth[j], cursors_shape, phase_shape,
            frames_shape, none, none);
      }
      cm_bv_phase_leaf(and_cases[1], cursors_shape, phase_shape,
          frames_shape, none, none);
    } else if (i == 5) {
      term op = cm_bv_constructor_arg(concrete_phase, 5, 0);
      term left_value = cm_bv_constructor_arg(concrete_phase, 5, 3);
      gnode_list or_cases = BOOL_CASES_TAC(
          branch, `${op:int} == 0i`, "Hbudget_v_result_or");
      gnode_list or_ok = BOOL_CASES_TAC(or_cases[0],
          `cm_binary_ok (p:cm_program) 0i
             ${left_value:cm_value} (v:cm_value) (st:cm_src_state)`,
          "Hbudget_v_result_or_ok");
      for (size_t j = 0; j < vector_size(or_ok); ++j) {
        cm_bv_phase_leaf(or_ok[j], cursors_shape, phase_shape,
            frames_shape, none, none);
      }
      gnode_list and_cases = BOOL_CASES_TAC(
          or_cases[1], `${op:int} == 1i`, "Hbudget_v_result_and");
      gnode_list and_ok = BOOL_CASES_TAC(and_cases[0],
          `cm_binary_ok (p:cm_program) 1i
             ${left_value:cm_value} (v:cm_value) (st:cm_src_state)`,
          "Hbudget_v_result_and_ok");
      for (size_t j = 0; j < vector_size(and_ok); ++j) {
        cm_bv_phase_leaf(and_ok[j], cursors_shape, phase_shape,
            frames_shape, none, none);
      }
      gnode_list other_ok = BOOL_CASES_TAC(and_cases[1],
          `cm_binary_ok (p:cm_program) ${op:int}
             ${left_value:cm_value} (v:cm_value) (st:cm_src_state)`,
          "Hbudget_v_result_other_ok");
      for (size_t j = 0; j < vector_size(other_ok); ++j) {
        cm_bv_phase_leaf(other_ok[j], cursors_shape, phase_shape,
            frames_shape, none, none);
      }
    } else if (i == 8) {
      term base = cm_bv_constructor_arg(concrete_phase, 2, 0);
      gnode_list shift_cases = BOOL_CASES_TAC(branch,
          `cm_ptr_shift_ok (cm_program_structs (p:cm_program))
             ${base:cm_value}
             (cm_value_number (st:cm_src_state) (v:cm_value))
             (st:cm_src_state)`,
          "Hbudget_v_shift");
      for (size_t j = 0; j < vector_size(shift_cases); ++j) {
        cm_bv_phase_leaf(shift_cases[j], cursors_shape, phase_shape,
            frames_shape, none, none);
      }
    } else if (i == 9) {
      term mid = cm_bv_constructor_arg(concrete_phase, 2, 0);
      gnode_list member_cases = BOOL_CASES_TAC(branch,
          `cm_ptr_member_ok (p:cm_program) (v:cm_value)
             ${mid:int} (st:cm_src_state)`,
          "Hbudget_v_member");
      for (size_t j = 0; j < vector_size(member_cases); ++j) {
        cm_bv_phase_leaf(member_cases[j], cursors_shape, phase_shape,
            frames_shape, none, none);
      }
    } else if (i == 14) {
      term slot = cm_bv_constructor_arg(concrete_phase, 1, 0);
      term init_ty =
          `cm_slot_ty
             (inth ${slot:int}
               (cm_function_locals
                 (inth (fid:int)
                   (cm_program_functions (p:cm_program)))))`;
      term init_ptr = `cm_state_env (st:cm_src_state) 1i ${slot:int}`;
      gnode_list address_cases = BOOL_CASES_TAC(branch,
          `cm_binding_address_ok (p:cm_program) (fid:int)
             1i ${slot:int} (st:cm_src_state)`,
          "Hbudget_v_init_address");
      for (size_t j = 0; j < vector_size(address_cases); ++j) {
        gnode_list store_cases = BOOL_CASES_TAC(address_cases[j],
            `cm_store_ok ${init_ty:cm_type} ${init_ptr:cm_value}
               (st:cm_src_state)`,
            "Hbudget_v_init_store");
        for (size_t k = 0; k < vector_size(store_cases); ++k) {
          cm_bv_phase_leaf(store_cases[k], cursors_shape, phase_shape,
              frames_shape, none, none);
        }
      }
    } else if (i == 17 || i == 18) {
      gnode_list truth_cases = BOOL_CASES_TAC(branch,
          `cm_truth (st:cm_src_state) (v:cm_value)`,
          i == 17 ? "Hbudget_v_if_truth" : "Hbudget_v_while_truth");
      for (size_t j = 0; j < vector_size(truth_cases); ++j) {
        cm_bv_phase_leaf(truth_cases[j], cursors_shape, phase_shape,
            frames_shape, none, none);
      }
    } else if (i == 21) {
      term callee = cm_bv_constructor_arg(concrete_phase, 8, 0);
      term rest = cm_bv_constructor_arg(concrete_phase, 8, 1);
      term values = cm_bv_constructor_arg(concrete_phase, 8, 2);
      gnode_list rest_cases = BOOL_CASES_TAC(
          branch, `${rest:(cm_expr)list} == []`,
          "Hbudget_v_arg_nil");
      gnode_list call_cases = BOOL_CASES_TAC(rest_cases[0],
          `cm_call_ok (p:cm_program) ${callee:int}
               (REVERSE ((v:cm_value) :: ${values:(cm_value)list}))
               (st:cm_src_state) &&
             cm_call_depth
               (cm_cursor_frames ${cursor_tail:(cm_acursor)list}) <
               65536i`,
          "Hbudget_v_call_ready");
      for (size_t j = 0; j < vector_size(call_cases); ++j) {
        cm_bv_phase_leaf(call_cases[j], cursors_shape, phase_shape,
            frames_shape, none, none);
      }
      gnode_list list_cases = DISJ_CASES_TAC(rest_cases[1],
          ispec_rule(rest, get_theorem_by_name("list_CASES")),
          "Hbudget_v_arg_shape");
      thm nil_shape = cm_bv_assumption(
          "Hbudget_v_arg_shape", list_cases[0]);
      CONTR_TAC(list_cases[0], not_elim_rule(
          assume_rule(mk_not(mk_eq(rest, `[]:(cm_expr)list`))),
          nil_shape));
      gnode cons = ASMP_EXISTS_TAC(
          list_cases[1], "Hbudget_v_arg_shape", NULL);
      cons = ASMP_EXISTS_TAC(cons, "Hbudget_v_arg_shape", NULL);
      thm rest_shape = cm_bv_assumption("Hbudget_v_arg_shape", cons);
      thm parts = cm_bv_arg_parts(
          cursors_shape, phase_shape, rest_shape);
      cm_bv_phase_leaf(cons, cursors_shape, phase_shape,
          frames_shape, THM_LIST(rest_shape), THM_LIST(parts));
    } else {
      cm_bv_phase_leaf(branch, cursors_shape, phase_shape,
          frames_shape, none, none);
    }
  }
}

PROOF static thm cm_prove_task_budget_v_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (v:cm_value)
          (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_annotation_erases (CMVTask p fid v st ks) ann ==>
         cm_task_type_ready p (CMVTask p fid v st ks) ann ==>
         cm_task_coordinate_ready p (CMVTask p fid v st ks) ann ==>
         cm_task_budget p (CMVTask p fid v st ks) ann ==>
         cm_task_budget p
           (cm_step (CMVTask p fid v st ks))
           (cm_update_annotation
             (cm_annotation_step (CMVTask p fid v st ks) ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  term cursors = `cm_ann_cursors (ann:cm_annotation)`;
  gnode_list cursor_cases = DISJ_CASES_TAC(introduced,
      ispec_rule(cursors, get_theorem_by_name("list_CASES")),
      "Hbudget_v_cursors");
  thm nil_shape = cm_bv_assumption(
      "Hbudget_v_cursors", cursor_cases[0]);
  thm impossible = cm_bv_normalize(THM_LIST(
      nil_shape, get_cm_task_type_ready_def(),
      get_cm_cursor_head_value_type_ready_def(),
      cm_ann_cursors_def),
      assume_rule(`cm_task_type_ready (p:cm_program)
        (CMVTask p (fid:int) (v:cm_value) (st:cm_src_state)
          (ks:(cm_frame)list)) (ann:cm_annotation)`));
  CONTR_TAC(cursor_cases[0], impossible);
  gnode cons = ASMP_EXISTS_TAC(
      cursor_cases[1], "Hbudget_v_cursors", NULL);
  cons = ASMP_EXISTS_TAC(cons, "Hbudget_v_cursors", NULL);
  thm cursors_shape = cm_bv_assumption("Hbudget_v_cursors", cons);
  term concrete_cursors = rhs_of(cursors_shape);
  term head_cursor = cm_bv_constructor_arg(concrete_cursors, 2, 0);
  term cursor_tail = cm_bv_constructor_arg(concrete_cursors, 2, 1);
  thm frames_forward = cm_bv_normalize(THM_LIST(
      cursors_shape, cm_annotation_erases_def,
      cm_cursor_frames_def, cm_ann_cursors_def,
      cm_cursor_phase_def, cm_phase_frame_def),
      assume_rule(`cm_annotation_erases
        (CMVTask (p:cm_program) (fid:int) (v:cm_value)
          (st:cm_src_state) (ks:(cm_frame)list))
        (ann:cm_annotation)`));
  cm_bv_split_phase(cons, cursors_shape,
      sym_rule(frames_forward), head_cursor, cursor_tail);
  return gnode_prove(root);
}
PROOF thm cm_task_budget_v_step =
    cm_prove_task_budget_v_step();

PROOF static int cmc_preservation_budget_value_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_budget_value_axioms_before,
      "cmc_preservation_budget_value introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_budget_value_checks =
    cmc_preservation_budget_value_final_checks();
