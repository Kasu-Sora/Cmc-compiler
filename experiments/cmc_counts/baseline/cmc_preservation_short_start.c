#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "userlib/proof_patterns.h"
#include "cmc_preservation_short_start.h"
#include "cmc_preservation_short_defs.h"
#include "cmc_preservation_short_bases.h"
#include "cmc_preservation_generation.h"

#require "userlib/proof_patterns.c"
#require "cmc_preservation_short_defs.c"
#require "cmc_preservation_short_bases.c"
#require "cmc_preservation_generation.c"

PROOF static size_t _cmc_preservation_short_start_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_ss_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_ss_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_ss_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_ss_named_shape(
    gnode *node, const char *label) {
  while (true) {
    labeled_term_list assumptions = goal_lasmps((*node)->g);
    int index = labeled_term_list_index(assumptions, label);
    if (!is_exists(assumptions[index].tm)) {
      return assume_rule(assumptions[index].tm);
    }
    *node = ASMP_EXISTS_TAC(*node, label, NULL);
  }
}

PROOF static thm cm_ss_same_region_bases(
    term old_state, term new_state, thm_list state_rules) {
  term limit = mk_comb(`cm_state_nextgen`, old_state);
  term proposition =
      mk_comb(mk_comb(mk_comb(`cm_region_bases_below_equal`,
        mk_comb(`cm_state_regions`, new_state)),
        mk_comb(`cm_state_regions`, old_state)), limit);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(state_rules), proposition);
  thm reflexive = specl_rule(TERM_LIST(
      mk_comb(`cm_state_regions`, old_state), limit),
      cm_region_bases_below_equal_refl);
  return eq_mp_rule(sym_rule(target_view), reflexive);
}

PROOF static thm cm_ss_transport_frames(
    term p, term fid, term old_state, term new_state,
    term frames, thm bases, thm generation, thm ready) {
  return match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        frames, p, fid, old_state, new_state,
        mk_comb(`cm_state_nextgen`, old_state)),
        cm_frames_short_ready_bases), bases), generation), ready);
}
PROOF static thm cm_prove_short_task_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(condition:bool) (yes:cm_task) (no:cm_task).
         cm_task_short_ready (if condition then yes else no) <=>
         (if condition
          then cm_task_short_ready yes
          else cm_task_short_ready no)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      introduced, `condition:bool`, "Hshort_condition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF static thm cm_short_task_cond =
    cm_prove_short_task_cond();
PROOF static thm cm_prove_short_frames_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (condition:bool)
         (yes:(cm_frame)list) (no:(cm_frame)list).
         cm_frames_short_ready st (if condition then yes else no) <=>
         (if condition
          then cm_frames_short_ready st yes
          else cm_frames_short_ready st no)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      introduced, `condition:bool`, "Hshort_frames_condition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF static thm cm_short_frames_cond =
    cm_prove_short_frames_cond();



PROOF static void cm_ss_accept(
    gnode branch, thm_list rules) {
  thm_list complete = (thm_list)vector_copy(rules);
  vector_add(&complete, cm_short_task_cond);
  vector_add(&complete, cm_short_frames_cond);
  labeled_term_list assumptions = goal_lasmps(branch->g);
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    vector_add(&complete, assume_rule(assumptions[i].tm));
  }
  ACCEPT_TAC(branch, eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(complete), goal_ccl(branch->g))));
}

PROOF static thm cm_prove_args_start_short_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (args:(cm_expr)list)
         (st:cm_src_state) (ks:(cm_frame)list)
         (callee:int) (ret:cm_type).
         cm_frames_generation_below p caller
           (cm_state_nextgen st) ks ==>
         cm_frames_short_ready st ks ==>
         cm_task_short_ready
           (cm_args_start p caller args st ks callee ret)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm old_generation = assume_rule(
      `cm_frames_generation_below (p:cm_program) (caller:int)
        (cm_state_nextgen (st:cm_src_state)) (ks:(cm_frame)list)`);
  thm old_ready = assume_rule(
      `cm_frames_short_ready (st:cm_src_state) (ks:(cm_frame)list)`);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`args:(cm_expr)list`, get_theorem_by_name("list_CASES")),
      "Hshort_args");
  {
    gnode nil = cases[0];
    thm args_nil = cm_ss_named_shape(&nil, "Hshort_args");
    term call_ok = `cm_call_ok (p:cm_program) (callee:int)
        ([]:(cm_value)list) (st:cm_src_state)`;
    gnode_list call_cases = BOOL_CASES_TAC(
        nil, call_ok, "Hshort_call_ok");
    for (size_t i = 0; i < vector_size(call_cases); ++i) {
      gnode_list depth_cases = BOOL_CASES_TAC(call_cases[i],
          `cm_call_depth (ks:(cm_frame)list) < 65536i`,
          i == 0 ? "Hshort_call_depth_yes" :
                   "Hshort_call_depth_no");
      for (size_t j = 0; j < vector_size(depth_cases); ++j) {
        thm entered = cm_ss_transport_frames(
            `p:cm_program`, `caller:int`, `st:cm_src_state`,
            `cm_enter_call (p:cm_program) (callee:int)
              ([]:(cm_value)list) (st:cm_src_state)`,
            `ks:(cm_frame)list`,
            specl_rule(TERM_LIST(
              `p:cm_program`, `callee:int`, `st:cm_src_state`,
              `[]:(cm_value)list`), cm_call_regions_bases),
            old_generation, old_ready);
        cm_ss_accept(depth_cases[j], THM_LIST(
            args_nil, get_cm_args_start_def(), get_cm_begin_call_def(),
            cm_task_short_ready_def, cm_frames_short_ready_def,
            cm_frame_short_ready_def, old_ready, entered,
            get_theorem_by_name("COND_ID")));
      }
    }
  }
  {
    gnode cons = cases[1];
    thm args_cons = cm_ss_named_shape(&cons, "Hshort_args");
    cm_ss_accept(cons, THM_LIST(
        args_cons, get_cm_args_start_def(), cm_task_short_ready_def,
        cm_frames_short_ready_def, cm_frame_short_ready_def,
        old_ready));
  }
  return gnode_prove(root);
}
PROOF static thm cm_args_start_short_ready =
    cm_prove_args_start_short_ready();

PROOF static void cm_ss_open_task_facts(
    term task, thm *frames_generation, thm *frames_ready) {
  thm generation_safe = conv_rule(rewrite_conv(THM_LIST(
      cm_task_generation_safe_def)), assume_rule(
        mk_comb(mk_comb(mk_comb(`cm_task_generation_safe`,
          `p:cm_program`), task), `ann:cm_annotation`)));
  thm task_generation = conjunct1_rule(generation_safe);
  thm opened_generation = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_generation_below_def)), task_generation);
  *frames_generation = conjunct2_rule(opened_generation);
  *frames_ready = conv_rule(rewrite_conv(THM_LIST(
      cm_task_short_ready_def)), assume_rule(
        mk_comb(`cm_task_short_ready`, task)));
}

PROOF static thm cm_prove_task_short_r_step(void) {
  term task = `CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
      (st:cm_src_state) (ks:(cm_frame)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_task_generation_safe p
           (CMRTask p fid expr st ks) ann ==>
         cm_task_short_ready (CMRTask p fid expr st ks) ==>
         cm_task_short_ready
           (cm_step (CMRTask p fid expr st ks))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm old_generation = empty_theorem;
  thm old_ready = empty_theorem;
  cm_ss_open_task_facts(task, &old_generation, &old_ready);
  thm io_bases = cm_ss_same_region_bases(
      `st:cm_src_state`,
      `cm_state_io (st:cm_src_state)
        (TL (cm_state_input st)) (cm_state_output st)`,
      get_cm_state_core_defs());
  thm io_ready = cm_ss_transport_frames(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `cm_state_io (st:cm_src_state)
        (TL (cm_state_input st)) (cm_state_output st)`,
      `ks:(cm_frame)list`, io_bases, old_generation, old_ready);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hshort_expr");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    thm shape = cm_ss_named_shape(&branch, "Hshort_expr");
    term concrete = rhs_of(shape);
    if (i == 8) {
      thm result = specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`,
          cm_ss_constructor_arg(concrete, 3, 1),
          `st:cm_src_state`, `ks:(cm_frame)list`,
          cm_ss_constructor_arg(concrete, 3, 0),
          cm_ss_constructor_arg(concrete, 3, 2)),
          cm_args_start_short_ready);
      result = match_mp_rule(result, old_generation);
      result = match_mp_rule(result, old_ready);
      gnode reduced = CONV_TAC(branch, rewrite_conv(THM_LIST(
          shape, get_cm_step_def(), get_cm_rstart_def())));
      ACCEPT_TAC(reduced, result);
      continue;
    }
    cm_ss_accept(branch, THM_LIST(
        shape, get_cm_step_def(), get_cm_rstart_def(),
        cm_task_short_ready_def, cm_frames_short_ready_def,
        cm_frame_short_ready_def, old_ready, io_ready,
        get_theorem_by_name("COND_ID")));
  }
  return gnode_prove(root);
}
PROOF thm cm_task_short_r_step =
    cm_prove_task_short_r_step();

PROOF static thm cm_prove_task_short_l_step(void) {
  term task = `CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
      (st:cm_src_state) (ks:(cm_frame)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_task_generation_safe p
           (CMLTask p fid expr st ks) ann ==>
         cm_task_short_ready (CMLTask p fid expr st ks) ==>
         cm_task_short_ready
           (cm_step (CMLTask p fid expr st ks))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm unused_generation = empty_theorem;
  thm old_ready = empty_theorem;
  cm_ss_open_task_facts(task, &unused_generation, &old_ready);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hshort_expr_l");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    thm shape = cm_ss_named_shape(&branch, "Hshort_expr_l");
    cm_ss_accept(branch, THM_LIST(
        shape, get_cm_step_def(), get_cm_lstart_def(),
        cm_task_short_ready_def, cm_frames_short_ready_def,
        cm_frame_short_ready_def, old_ready,
        get_theorem_by_name("COND_ID")));
  }
  return gnode_prove(root);
}
PROOF thm cm_task_short_l_step =
    cm_prove_task_short_l_step();

PROOF static thm cm_prove_task_short_s_step(void) {
  term task = `CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
      (st:cm_src_state) (ks:(cm_frame)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (stmt:cm_stmt)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_task_generation_safe p
           (CMSTask p fid stmt st ks) ann ==>
         cm_task_short_ready (CMSTask p fid stmt st ks) ==>
         cm_task_short_ready
           (cm_step (CMSTask p fid stmt st ks))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm old_generation = empty_theorem;
  thm old_ready = empty_theorem;
  cm_ss_open_task_facts(task, &old_generation, &old_ready);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`stmt:cm_stmt`, get_datatype_cases("cm_stmt")),
      "Hshort_stmt");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    thm shape = cm_ss_named_shape(&branch, "Hshort_stmt");
    term concrete = rhs_of(shape);
    if (i == 2 || i == 3) {
      term slot = cm_ss_constructor_arg(concrete,
          i == 2 ? 1 : 2, 0);
      thm activated_ready = cm_ss_transport_frames(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `cm_activate_local (p:cm_program) (fid:int)
            ${slot:int} (st:cm_src_state)`,
          `ks:(cm_frame)list`,
          specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, slot, `st:cm_src_state`),
            cm_activate_local_region_bases),
          old_generation, old_ready);
      gnode_list slot_cases = BOOL_CASES_TAC(branch,
          `cm_local_slot_ok (p:cm_program) (fid:int) ${slot:int}`,
          i == 2 ? "Hshort_decl_slot" : "Hshort_init_slot");
      for (size_t j = 0; j < vector_size(slot_cases); ++j) {
        cm_ss_accept(slot_cases[j], THM_LIST(
            shape, get_cm_step_def(), get_cm_sstart_def(),
            cm_task_short_ready_def, cm_frames_short_ready_def,
            cm_frame_short_ready_def, old_ready, activated_ready,
            get_theorem_by_name("COND_ID")));
      }
      continue;
    }
    cm_ss_accept(branch, THM_LIST(
        shape, get_cm_step_def(), get_cm_sstart_def(),
        cm_task_short_ready_def, cm_frames_short_ready_def,
        cm_frame_short_ready_def, old_ready,
        get_theorem_by_name("COND_ID")));
  }
  return gnode_prove(root);
}
PROOF thm cm_task_short_s_step =
    cm_prove_task_short_s_step();

PROOF static int cmc_preservation_short_start_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_short_start_axioms_before,
      "cmc_preservation_short_start introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_short_start_checks =
    cmc_preservation_short_start_final_checks();
