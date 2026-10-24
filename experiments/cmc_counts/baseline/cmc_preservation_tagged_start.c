#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_tagged_start.h"

#require "cmc_preservation_tagged_transition.c"

PROOF static size_t _cmc_preservation_tagged_start_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_tgs_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_tgs_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_tgs_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static gnode cm_tgs_open_shape(
    gnode branch, const char *label) {
  while (true) {
    labeled_term_list assumptions = goal_lasmps(branch->g);
    int index = labeled_term_list_index(assumptions, label);
    if (!is_exists(assumptions[index].tm)) break;
    branch = ASMP_EXISTS_TAC(branch, label, NULL);
  }
  return branch;
}

PROOF static thm cm_tgs_shape(gnode branch, const char *label) {
  labeled_term_list assumptions = goal_lasmps(branch->g);
  return assume_rule(assumptions[
      labeled_term_list_index(assumptions, label)].tm);
}

PROOF static void cm_tgs_accept_normalized(
    gnode branch, thm source, thm_list rules) {
  thm normalized = conv_rule(reduce_rewrite_conv(rules), source);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
}

PROOF static thm cm_prove_task_tagged_valid_cond(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(condition:bool) (left:cm_task) (right:cm_task).
         cm_task_tagged_valid (if condition then left else right) <=>
         (if condition
          then cm_task_tagged_valid left
          else cm_task_tagged_valid right)`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `condition:bool`, "Hcondition");
  CONV_WITH_ASMP_TAC(cases[0], reduce_rewrite_conv, THM_LIST());
  CONV_WITH_ASMP_TAC(cases[1], reduce_rewrite_conv, THM_LIST());
  return gnode_prove(root_node);
}
PROOF thm cm_task_tagged_valid_cond =
    cm_prove_task_tagged_valid_cond();

PROOF static thm cm_prove_tagged_span_rstart(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_typed_program p ==>
         cm_state_generation_below p fid st ==>
         cm_runtime_core p fid st ann ==>
         cm_tagged_span_valid st ==>
         cm_task_tagged_valid (cm_rstart p fid expr st ks)`);
  gnode introduced = AUTO_INTROS_TAC(root_node);
  gnode_list cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()),
      "Hexpr");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cm_tgs_open_shape(cases[i], "Hexpr");
    thm shape = cm_tgs_shape(branch, "Hexpr");
    term concrete = rhs_of(shape);
    if (i == 8) {
      term callee = cm_tgs_constructor_arg(concrete, 3, 0);
      term args = cm_tgs_constructor_arg(concrete, 3, 1);
      term ret = cm_tgs_constructor_arg(concrete, 3, 2);
      gnode_list arg_cases = DISJ_CASES_TAC(
          branch,
          ispec_rule(args, get_theorem_by_name("list_CASES")),
          "Hargs");
      {
        thm args_nil = cm_tgs_shape(arg_cases[0], "Hargs");
        thm result = specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, callee,
            `[]:(cm_value)list`, `st:cm_src_state`, ret,
            `ks:(cm_frame)list`, `ann:cm_annotation`),
            cm_tagged_span_begin_call_runtime);
        result = match_mp_rule(result, assume_rule(
            `cm_typed_program (p:cm_program)`));
        result = match_mp_rule(result, assume_rule(
            `cm_state_generation_below (p:cm_program) (fid:int)
              (st:cm_src_state)`));
        result = match_mp_rule(result, assume_rule(
            `cm_runtime_core (p:cm_program) (fid:int)
              (st:cm_src_state) (ann:cm_annotation)`));
        result = match_mp_rule(result, assume_rule(
            `cm_tagged_span_valid (st:cm_src_state)`));
        gnode reduced = CONV_TAC(arg_cases[0],
            reduce_rewrite_conv(THM_LIST(
              shape, args_nil, get_cm_rstart_def(),
              get_cm_args_start_def())));
        ACCEPT_TAC(reduced, result);
      }
      {
        gnode cons = ASMP_EXISTS_TAC(arg_cases[1], "Hargs", NULL);
        cons = ASMP_EXISTS_TAC(cons, "Hargs", NULL);
        thm args_cons = cm_tgs_shape(cons, "Hargs");
        cm_tgs_accept_normalized(cons,
            assume_rule(`cm_tagged_span_valid (st:cm_src_state)`),
            THM_LIST(shape, args_cons, get_cm_rstart_def(),
              get_cm_args_start_def(), cm_task_tagged_valid_def));
      }
    } else if (i == 10) {
      term input_nil_term =
          `(cm_state_input (st:cm_src_state) == ([]:(int)list))`;
      gnode_list input_cases = BOOL_CASES_TAC(
          branch, input_nil_term, "Hinput_nil");
      {
        thm input_nil = assume_rule(input_nil_term);
        cm_tgs_accept_normalized(input_cases[0],
            assume_rule(`cm_tagged_span_valid (st:cm_src_state)`),
            THM_LIST(shape, input_nil, get_cm_rstart_def(),
              cm_task_tagged_valid_def));
      }
      {
        thm not_input_nil = assume_rule(mk_not(input_nil_term));
        gnode_list byte_cases = BOOL_CASES_TAC(input_cases[1],
            `tower_byte_value
              (HD (cm_state_input (st:cm_src_state)))`,
            "Hinput_byte");
        thm byte = assume_rule(
            `tower_byte_value
              (HD (cm_state_input (st:cm_src_state)))`);
        thm io_valid = specl_rule(TERM_LIST(
            `st:cm_src_state`, `TL (cm_state_input (st:cm_src_state))`,
            `cm_state_output (st:cm_src_state)`), cm_tagged_span_io);
        io_valid = match_mp_rule(io_valid, assume_rule(
            `cm_tagged_span_valid (st:cm_src_state)`));
        gnode reduced = CONV_TAC(byte_cases[0],
            reduce_rewrite_conv(THM_LIST(
              shape, not_input_nil, byte, get_cm_rstart_def(),
              cm_task_tagged_valid_def)));
        ACCEPT_TAC(reduced, io_valid);
        cm_tgs_accept_normalized(byte_cases[1],
            assume_rule(`cm_tagged_span_valid (st:cm_src_state)`),
            THM_LIST(shape, not_input_nil, assume_rule(mk_not(
                `tower_byte_value
                  (HD (cm_state_input (st:cm_src_state)))`)),
              get_cm_rstart_def(), cm_task_tagged_valid_def));
      }
    } else {
      cm_tgs_accept_normalized(branch,
          assume_rule(`cm_tagged_span_valid (st:cm_src_state)`),
          THM_LIST(shape, get_cm_rstart_def(),
            get_cm_args_start_def(), cm_task_tagged_valid_cond,
            cm_task_tagged_valid_def, get_theorem_by_name("COND_ID")));
    }
  }
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_rstart = cm_prove_tagged_span_rstart();

PROOF static thm cm_prove_tagged_span_lstart(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_tagged_span_valid st ==>
         cm_task_tagged_valid (cm_lstart p fid expr st ks)`);
  gnode introduced = AUTO_INTROS_TAC(root_node);
  gnode_list cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()),
      "Hexpr");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cm_tgs_open_shape(cases[i], "Hexpr");
    thm shape = cm_tgs_shape(branch, "Hexpr");
    cm_tgs_accept_normalized(branch,
        assume_rule(`cm_tagged_span_valid (st:cm_src_state)`),
        THM_LIST(shape, get_cm_lstart_def(),
          cm_task_tagged_valid_cond, cm_task_tagged_valid_def,
          get_theorem_by_name("COND_ID")));
  }
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_lstart = cm_prove_tagged_span_lstart();

PROOF static thm cm_prove_tagged_span_sstart(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (stmt:cm_stmt)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         cm_tagged_span_valid st ==>
         cm_task_tagged_valid (cm_sstart p fid stmt st ks)`);
  gnode introduced = AUTO_INTROS_TAC(root_node);
  gnode_list cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`stmt:cm_stmt`, get_cm_stmt_cases()),
      "Hstmt");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cm_tgs_open_shape(cases[i], "Hstmt");
    thm shape = cm_tgs_shape(branch, "Hstmt");
    term concrete = rhs_of(shape);
    if (i == 2 || i == 3) {
      size_t arity = i == 2 ? 1 : 2;
      term slot = cm_tgs_constructor_arg(concrete, arity, 0);
      term local_ok_term =
          `cm_local_slot_ok (p:cm_program) (fid:int) ${slot:int}`;
      gnode_list local_cases = BOOL_CASES_TAC(
          branch, local_ok_term, "Hlocal_ok");
      {
        thm local_ok = assume_rule(local_ok_term);
        thm activated = specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, slot, `st:cm_src_state`),
            cm_tagged_span_activate_local);
        activated = match_mp_rule(activated, assume_rule(
            `cm_regions_before (cm_state_regions (st:cm_src_state))
              (cm_state_nextgen st)`));
        activated = match_mp_rule(activated, assume_rule(
            `cm_tagged_span_valid (st:cm_src_state)`));
        gnode reduced = CONV_TAC(local_cases[0],
            reduce_rewrite_conv(THM_LIST(
              shape, local_ok, get_cm_sstart_def(),
              cm_task_tagged_valid_def)));
        ACCEPT_TAC(reduced, activated);
      }
      {
        thm not_local_ok = assume_rule(mk_not(local_ok_term));
        cm_tgs_accept_normalized(local_cases[1],
            assume_rule(`cm_tagged_span_valid (st:cm_src_state)`),
            THM_LIST(shape, not_local_ok, get_cm_sstart_def(),
              cm_task_tagged_valid_def));
      }
    } else {
      cm_tgs_accept_normalized(branch,
          assume_rule(`cm_tagged_span_valid (st:cm_src_state)`),
          THM_LIST(shape, get_cm_sstart_def(),
            cm_task_tagged_valid_cond, cm_task_tagged_valid_def,
            get_theorem_by_name("COND_ID")));
    }
  }
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_sstart = cm_prove_tagged_span_sstart();

PROOF static int cmc_preservation_tagged_start_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_tagged_start_axioms_before,
      "cmc_preservation_tagged_start introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_rstart)) == 0,
      "rstart tagged-span theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_lstart)) == 0,
      "lstart tagged-span theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_sstart)) == 0,
      "sstart tagged-span theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_tagged_start_checks =
    cmc_preservation_tagged_start_final_checks();
