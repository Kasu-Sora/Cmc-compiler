#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_generation_step_start.h"
#include "cmc_preservation_generation_state.h"
#include "cmc_preservation_generation_frame.h"
#include "cmc_preservation_generation_task.h"

#require "cmc_preservation_generation_state.c"
#require "cmc_preservation_generation_frame.c"
#require "cmc_preservation_generation_task.c"

PROOF static size_t _cmc_preservation_generation_step_start_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_task_generation_below_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (condition:bool) (yes:cm_task) (no:cm_task).
         cm_task_generation_below p (if condition then yes else no) <=>
         (if condition
          then cm_task_generation_below p yes
          else cm_task_generation_below p no)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      introduced, `condition:bool`, "Hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF static thm cm_task_generation_below_cond =
    cm_prove_task_generation_below_cond();

PROOF static thm cm_prove_frames_generation_below_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (limit:int) (condition:bool)
         (yes:(cm_frame)list) (no:(cm_frame)list).
         cm_frames_generation_below p fid limit
           (if condition then yes else no) <=>
         (if condition
          then cm_frames_generation_below p fid limit yes
          else cm_frames_generation_below p fid limit no)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      introduced, `condition:bool`, "Hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF static thm cm_frames_generation_below_cond =
    cm_prove_frames_generation_below_cond();

PROOF static thm cm_prove_state_nextgen_io(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (input:(int)list) (output:(int)list).
         cm_state_nextgen (cm_state_io st input output) ==
         cm_state_nextgen st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_state_io_def());
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF thm cm_state_nextgen_io =
    cm_prove_state_nextgen_io();

PROOF static thm cm_prove_state_nextgen_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (ptr:cm_value) (v:cm_value) (st:cm_src_state).
         cm_state_nextgen (cm_state_store ty ptr v st) ==
         cm_state_nextgen st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_state_store_def());
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF thm cm_state_nextgen_store =
    cm_prove_state_nextgen_store();

PROOF static thm cm_prove_state_nextgen_store_params(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(cm_value)list) (p:cm_program) (fid:int)
         (index:int) (st:cm_src_state).
         cm_state_nextgen (cm_store_params p fid values index st) ==
         cm_state_nextgen st`);
  gnode_list cases = INDUCT_TAC(root, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_store_params_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term stored =
        `cm_state_store
          (cm_slot_ty (inth (index:int)
            (cm_function_params
              (inth (fid:int) (cm_program_functions (p:cm_program))))))
          (cm_state_env (st:cm_src_state) 2i index) (a0:cm_value) st`;
    thm ih = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `(index:int) + 1i`, stored),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    thm result = conv_rule(rewrite_conv(THM_LIST(
        cm_state_nextgen_store)), ih);
    gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        get_cm_store_params_def())));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF static thm cm_state_nextgen_store_params =
    cm_prove_state_nextgen_store_params();

PROOF static thm cm_prove_state_nextgen_activate_local(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (slot:int) (st:cm_src_state).
         cm_state_nextgen (cm_activate_local p fid slot st) ==
         cm_state_nextgen st + 1i`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_activate_local_def());
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF thm cm_state_nextgen_activate_local =
    cm_prove_state_nextgen_activate_local();

PROOF static thm cm_prove_state_nextgen_call_base(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state).
         cm_state_nextgen (cm_call_base_state p fid st) ==
         cm_state_nextgen st +
           ilength (cm_function_params
             (inth fid (cm_program_functions p)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_call_base_state_def());
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF static thm cm_state_nextgen_call_base =
    cm_prove_state_nextgen_call_base();

PROOF static thm cm_prove_state_nextgen_enter_call(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (values:(cm_value)list)
         (st:cm_src_state).
         cm_state_nextgen (cm_enter_call p fid values st) ==
         cm_state_nextgen st +
           ilength (cm_function_params
             (inth fid (cm_program_functions p)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm params = specl_rule(TERM_LIST(
      `values:(cm_value)list`, `p:cm_program`, `fid:int`, `0i:int`,
      `cm_call_base_state (p:cm_program) (fid:int) (st:cm_src_state)`),
      cm_state_nextgen_store_params);
  thm result = conv_rule(rewrite_conv(THM_LIST(
      cm_state_nextgen_call_base)), params);
  gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      get_cm_enter_call_def())));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}
PROOF thm cm_state_nextgen_enter_call =
    cm_prove_state_nextgen_enter_call();

PROOF static thm cm_prove_binding_value_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (scope:int) (slot:int)
         (st:cm_src_state).
         cm_state_generation_below p fid st ==>
         cm_binding_valid p
           (inth fid (cm_program_functions p)) scope slot ==>
         cm_value_generation_below (cm_state_nextgen st)
           (if scope == 0i then cm_global_pointer p slot
            else cm_state_env st scope slot)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm state_open = conv_rule(rewrite_conv(THM_LIST(
      cm_state_generation_below_def)), assume_rule(
        `cm_state_generation_below (p:cm_program) (fid:int)
          (st:cm_src_state)`));
  thm env_open = conv_rule(rewrite_conv(THM_LIST(
      cm_env_generation_below_def)),
      conjunct1_rule(conjunct2_rule(state_open)));
  thm binding = assume_rule(
      `cm_binding_valid (p:cm_program)
        (inth (fid:int) (cm_program_functions p))
        (scope:int) (slot:int)`);
  gnode_list global_cases = BOOL_CASES_TAC(
      leaf, `(scope:int) == 0i`, "Hglobal");
  {
    thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_binding_valid_def(),
        assume_rule(`(scope:int) == 0i`))), binding);
    thm pointer = specl_rule(TERM_LIST(`p:cm_program`, `slot:int`),
        cm_global_pointer_generation_below);
    pointer = match_mp_rule(pointer, conjunct1_rule(opened));
    pointer = match_mp_rule(pointer, conjunct2_rule(opened));
    thm result = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `cm_global_pointer (p:cm_program) (slot:int)`,
        `cm_first_dynamic_generation (p:cm_program)`,
        `cm_state_nextgen (st:cm_src_state)`),
        cm_value_generation_below_mono), conjunct1_rule(state_open)), pointer);
    gnode reduced = CONV_WITH_ASMP_TAC(global_cases[0],
        reduce_rewrite_conv, THM_LIST());
    ACCEPT_TAC(reduced, result);
  }
  gnode_list local_cases = BOOL_CASES_TAC(
      global_cases[1], `(scope:int) == 1i`, "Hlocal");
  {
    thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_binding_valid_def(),
        eqf_intro_rule(assume_rule(`~((scope:int) == 0i)`)),
        assume_rule(`(scope:int) == 1i`))), binding);
    thm result = match_mp_rule(spec_rule(`slot:int`,
        conjunct1_rule(conjunct2_rule(env_open))), opened);
    gnode reduced = CONV_WITH_ASMP_TAC(local_cases[0],
        reduce_rewrite_conv, THM_LIST());
    ACCEPT_TAC(reduced, result);
  }
  {
    thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_binding_valid_def(),
        eqf_intro_rule(assume_rule(`~((scope:int) == 0i)`)),
        eqf_intro_rule(assume_rule(`~((scope:int) == 1i)`)))), binding);
    thm scope_two = conjunct1_rule(opened);
    thm bounds = conjunct2_rule(opened);
    thm result = match_mp_rule(spec_rule(`slot:int`,
        conjunct2_rule(conjunct2_rule(env_open))), bounds);
    result = conv_rule(rewrite_conv(THM_LIST(scope_two)), result);
    gnode reduced = CONV_WITH_ASMP_TAC(local_cases[1],
        reduce_rewrite_conv, THM_LIST(scope_two));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_binding_value_generation_below =
    cm_prove_binding_value_generation_below();

PROOF static thm cm_prove_begin_call_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (fid:int)
         (values:(cm_value)list) (st:cm_src_state) (ret:cm_type)
         (ks:(cm_frame)list).
         cm_state_generation_below p caller st ==>
         cm_values_generation_below (cm_state_nextgen st) values ==>
         cm_frames_generation_below p caller (cm_state_nextgen st) ks ==>
         cm_task_generation_below p
           (cm_begin_call p caller fid values st ret ks)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_state = assume_rule(
      `cm_state_generation_below (p:cm_program) (caller:int)
        (st:cm_src_state)`);
  thm values_below = assume_rule(
      `cm_values_generation_below (cm_state_nextgen (st:cm_src_state))
        (values:(cm_value)list)`);
  thm old_frames = assume_rule(
      `cm_frames_generation_below (p:cm_program) (caller:int)
        (cm_state_nextgen (st:cm_src_state)) (ks:(cm_frame)list)`);
  thm entered = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `caller:int`, `fid:int`, `values:(cm_value)list`,
      `st:cm_src_state`), cm_state_generation_enter_call), old_state),
      values_below);
  thm nextgen = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `values:(cm_value)list`,
      `st:cm_src_state`), cm_state_nextgen_enter_call);
  term params =
      `cm_function_params
        (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  thm params_nonnegative = ispec_rule(
      params, get_theorem_by_name("ILENGTH_NONNEG"));
  thm old_le_sum = mp_rule(int_arith_rule(
      `0i <= ilength ${params:(cm_slot_d)list} ==>
       cm_state_nextgen (st:cm_src_state) <=
         cm_state_nextgen st + ilength ${params:(cm_slot_d)list}`),
      params_nonnegative);
  thm growth_view = beta_norm(ap_term_rule(
      `\new_limit:int.
         cm_state_nextgen (st:cm_src_state) <= new_limit`,
      nextgen));
  thm growth = eq_mp_rule(sym_rule(growth_view), old_le_sum);
  thm frames_grown = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `ks:(cm_frame)list`, `p:cm_program`, `caller:int`,
      `cm_state_nextgen (st:cm_src_state)`,
      `cm_state_nextgen
        (cm_enter_call p (fid:int) (values:(cm_value)list) st)`),
      cm_frames_generation_below_mono), growth), old_frames);
  thm old_open = conv_rule(rewrite_conv(THM_LIST(
      cm_state_generation_below_def)), old_state);
  thm old_env = conjunct1_rule(conjunct2_rule(old_open));
  thm grown_env = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `caller:int`,
      `cm_state_env (st:cm_src_state)`,
      `cm_state_nextgen (st:cm_src_state)`,
      `cm_state_nextgen
        (cm_enter_call p (fid:int) (values:(cm_value)list) st)`),
      get_cm_env_generation_below_mono()), growth), old_env);
  thm call_frame = conj_rule(grown_env, frames_grown);
  thm call_frames = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_frames_generation_below_def,
        cm_frame_generation_below_def, cm_frame_parent_fid_def)),
      `cm_frames_generation_below (p:cm_program) (fid:int)
        (cm_state_nextgen
          (cm_enter_call p fid (values:(cm_value)list) (st:cm_src_state)))
        (CMCallK (caller:int) (cm_state_env st) (cm_state_fp st)
          (cm_state_regions st) (ret:cm_type) :: (ks:(cm_frame)list))`)),
      call_frame);
  thm success = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_task_generation_below_def,
        entered, call_frames)),
      `cm_task_generation_below (p:cm_program)
        (CMSTask p (fid:int)
          (cm_function_body (inth fid (cm_program_functions p)))
          (cm_enter_call p fid (values:(cm_value)list) (st:cm_src_state))
          (CMCallK (caller:int) (cm_state_env st) (cm_state_fp st)
            (cm_state_regions st) (ret:cm_type) :: (ks:(cm_frame)list)))`));
  thm failure = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_task_generation_below_def,
        cm_control_generation_below_def, old_state, old_frames)),
      `cm_task_generation_below (p:cm_program)
        (CMCTask p (caller:int) (CMError 1i) (st:cm_src_state)
          (ks:(cm_frame)list))`));
  thm result = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_begin_call_def(),
        cm_task_generation_below_cond, success, failure,
        get_theorem_by_name("COND_ID"))),
      goal_ccl(leaf->g)));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_begin_call_generation_below =
    cm_prove_begin_call_generation_below();

PROOF static thm cm_prove_args_start_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (args:(cm_expr)list)
         (st:cm_src_state) (ks:(cm_frame)list) (callee:int)
         (ret:cm_type).
         cm_state_generation_below p caller st ==>
         cm_frames_generation_below p caller (cm_state_nextgen st) ks ==>
         cm_task_generation_below p
           (cm_args_start p caller args st ks callee ret)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`args:(cm_expr)list`,
        get_theorem_by_name("list_CASES")), "Hargs");
  {
    thm shape = assume_rule(
        goal_lasmps(cases[0]->g)[labeled_term_list_index(
          goal_lasmps(cases[0]->g), "Hargs")].tm);
    thm result = specl_rule(TERM_LIST(
        `p:cm_program`, `caller:int`, `callee:int`,
        `[]:(cm_value)list`, `st:cm_src_state`, `ret:cm_type`,
        `ks:(cm_frame)list`), cm_begin_call_generation_below);
    result = match_mp_rule(result, assume_rule(
        `cm_state_generation_below (p:cm_program) (caller:int)
          (st:cm_src_state)`));
    result = match_mp_rule(result, eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(cm_values_generation_below_def)),
        `cm_values_generation_below
          (cm_state_nextgen (st:cm_src_state)) ([]:(cm_value)list)`)));
    result = match_mp_rule(result, assume_rule(
        `cm_frames_generation_below (p:cm_program) (caller:int)
          (cm_state_nextgen (st:cm_src_state)) (ks:(cm_frame)list)`));
    result = conv_rule(rewrite_conv(THM_LIST(shape,
        get_cm_args_start_def())), result);
    gnode reduced = CONV_TAC(cases[0], rewrite_conv(THM_LIST(
        shape, get_cm_args_start_def())));
    ACCEPT_TAC(reduced, result);
  }
  {
    gnode cons_case = ASMP_EXISTS_TAC(cases[1], "Hargs", "head");
    cons_case = ASMP_EXISTS_TAC(cons_case, "Hargs", "tail");
    thm shape = assume_rule(
        goal_lasmps(cons_case->g)[labeled_term_list_index(
          goal_lasmps(cons_case->g), "Hargs")].tm);
    thm result = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(shape, get_cm_args_start_def(),
          cm_task_generation_below_def, cm_frames_generation_below_def,
          cm_frame_generation_below_def, cm_frame_parent_fid_def,
          cm_values_generation_below_def,
          assume_rule(
            `cm_state_generation_below (p:cm_program) (caller:int)
              (st:cm_src_state)`),
          assume_rule(
            `cm_frames_generation_below (p:cm_program) (caller:int)
              (cm_state_nextgen (st:cm_src_state))
              (ks:(cm_frame)list)`))),
        goal_ccl(cons_case->g)));
    ACCEPT_TAC(cons_case, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_args_start_generation_below =
    cm_prove_args_start_generation_below();

PROOF static term cm_ggs_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_ggs_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_ggs_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_generation_int_value(term limit, term value) {
  return eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_value_generation_below_def)),
      mk_comb(mk_comb(`cm_value_generation_below`,
        limit), value)));
}

PROOF static thm cm_prove_rstart_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_expr_static_valid p
           (inth fid (cm_program_functions p)) expr ==>
         cm_state_generation_below p fid st ==>
         cm_frames_generation_below p fid (cm_state_nextgen st) ks ==>
         cm_task_generation_below p (cm_rstart p fid expr st ks)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm old_state = assume_rule(
      `cm_state_generation_below (p:cm_program) (fid:int)
        (st:cm_src_state)`);
  thm old_frames = assume_rule(
      `cm_frames_generation_below (p:cm_program) (fid:int)
        (cm_state_nextgen (st:cm_src_state)) (ks:(cm_frame)list)`);
  thm static_expr = assume_rule(
      `cm_expr_static_valid (p:cm_program)
        (inth (fid:int) (cm_program_functions p)) (expr:cm_expr)`);
  thm state_open = conv_rule(rewrite_conv(THM_LIST(
      cm_state_generation_below_def)), old_state);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hex");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hex");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hex", NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hex")].tm);
    term concrete = rhs_of(shape);
    if (i == 8) {
      thm result = specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`,
          cm_ggs_constructor_arg(concrete, 3, 1),
          `st:cm_src_state`, `ks:(cm_frame)list`,
          cm_ggs_constructor_arg(concrete, 3, 0),
          cm_ggs_constructor_arg(concrete, 3, 2)),
          cm_args_start_generation_below);
      result = match_mp_rule(result, old_state);
      result = match_mp_rule(result, old_frames);
      result = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_rstart_def())), result);
      gnode reduced = CONV_TAC(branch, rewrite_conv(THM_LIST(
          shape, get_cm_rstart_def())));
      ACCEPT_TAC(reduced, result);
      continue;
    }
    thm_list rules = THM_LIST(
        shape, get_cm_rstart_def(), cm_task_generation_below_cond,
        cm_frames_generation_below_cond,
        cm_task_generation_below_def,
        cm_frames_generation_below_def,
        cm_frame_generation_below_def, cm_frame_parent_fid_def,
        cm_control_generation_below_def, cm_values_generation_below_def,
        old_state, old_frames, get_theorem_by_name("COND_ID"));
    if (i == 0) {
      term value = cm_ggs_constructor_arg(concrete, 2, 0);
      term ty = cm_ggs_constructor_arg(concrete, 2, 1);
      thm plain = cm_generation_int_value(
          `cm_state_nextgen (st:cm_src_state)`,
          mk_comb(`CMIntV`, value));
      thm converted = match_mp_rule(specl_rule(TERM_LIST(
          `st:cm_src_state`, ty, mk_comb(`CMIntV`, value),
          `cm_state_nextgen (st:cm_src_state)`),
          cm_convert_generation_below), plain);
      vector_add(&rules, converted);
    } else if (i == 1) {
      term sid = cm_ggs_constructor_arg(concrete, 2, 0);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, cm_expr_static_valid_def)), static_expr);
      thm pointer = specl_rule(TERM_LIST(`p:cm_program`, sid),
          cm_string_pointer_generation_below);
      pointer = match_mp_rule(pointer, conjunct1_rule(opened));
      pointer = match_mp_rule(pointer, conjunct2_rule(opened));
      thm grown = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
          mk_comb(mk_comb(`cm_string_pointer`, `p:cm_program`), sid),
          `cm_first_dynamic_generation (p:cm_program)`,
          `cm_state_nextgen (st:cm_src_state)`),
          cm_value_generation_below_mono), conjunct1_rule(state_open)),
          pointer);
      vector_add(&rules, grown);
    } else if (i == 2) {
      term scope = cm_ggs_constructor_arg(concrete, 3, 0);
      term slot = cm_ggs_constructor_arg(concrete, 3, 1);
      thm binding = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, cm_expr_static_valid_def)), static_expr);
      thm value = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, scope, slot, `st:cm_src_state`),
          cm_binding_value_generation_below), old_state), binding);
      vector_add(&rules, value);
    } else if (i == 9) {
      term asked = cm_ggs_constructor_arg(concrete, 2, 0);
      vector_add(&rules, cm_generation_int_value(
          `cm_state_nextgen (st:cm_src_state)`,
          mk_comb(`CMIntV`,
            mk_comb(mk_comb(`cm_type_size`,
              mk_comb(`cm_program_structs`, `p:cm_program`)), asked))));
    } else if (i == 10) {
      thm input_state = match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `TL (cm_state_input (st:cm_src_state))`,
          `cm_state_output (st:cm_src_state)`),
          cm_state_generation_io), old_state);
      vector_add(&rules, input_state);
      vector_add(&rules, cm_generation_int_value(
          `cm_state_nextgen (st:cm_src_state)`, `CMIntV (--1i)`));
      vector_add(&rules, cm_generation_int_value(
          `cm_state_nextgen (st:cm_src_state)`,
          `CMIntV (HD (cm_state_input (st:cm_src_state)))`));
      vector_add(&rules, specl_rule(TERM_LIST(
          `st:cm_src_state`, `TL (cm_state_input (st:cm_src_state))`,
          `cm_state_output (st:cm_src_state)`), cm_state_nextgen_io));
    }
    thm result = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(branch->g)));
    ACCEPT_TAC(branch, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_rstart_generation_below =
    cm_prove_rstart_generation_below();

PROOF static thm cm_prove_lstart_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_expr_static_valid p
           (inth fid (cm_program_functions p)) expr ==>
         cm_state_generation_below p fid st ==>
         cm_frames_generation_below p fid (cm_state_nextgen st) ks ==>
         cm_task_generation_below p (cm_lstart p fid expr st ks)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm old_state = assume_rule(
      `cm_state_generation_below (p:cm_program) (fid:int)
        (st:cm_src_state)`);
  thm old_frames = assume_rule(
      `cm_frames_generation_below (p:cm_program) (fid:int)
        (cm_state_nextgen (st:cm_src_state)) (ks:(cm_frame)list)`);
  thm static_expr = assume_rule(
      `cm_expr_static_valid (p:cm_program)
        (inth (fid:int) (cm_program_functions p)) (expr:cm_expr)`);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hex");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hex");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hex", NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hex")].tm);
    thm_list rules = THM_LIST(
        shape, get_cm_lstart_def(), cm_task_generation_below_cond,
        cm_frames_generation_below_cond,
        cm_task_generation_below_def,
        cm_frames_generation_below_def,
        cm_frame_generation_below_def, cm_frame_parent_fid_def,
        cm_control_generation_below_def, old_state, old_frames,
        get_theorem_by_name("COND_ID"));
    if (i == 2) {
      term concrete = rhs_of(shape);
      term scope = cm_ggs_constructor_arg(concrete, 3, 0);
      term slot = cm_ggs_constructor_arg(concrete, 3, 1);
      thm binding = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, cm_expr_static_valid_def)), static_expr);
      thm value = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, scope, slot, `st:cm_src_state`),
          cm_binding_value_generation_below), old_state), binding);
      vector_add(&rules, value);
    }
    thm result = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(branch->g)));
    ACCEPT_TAC(branch, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_lstart_generation_below =
    cm_prove_lstart_generation_below();

PROOF static thm cm_prove_frames_generation_activate_local(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (slot:int) (st:cm_src_state)
         (ks:(cm_frame)list).
         cm_frames_generation_below p fid (cm_state_nextgen st) ks ==>
         cm_frames_generation_below p fid
           (cm_state_nextgen (cm_activate_local p fid slot st)) ks`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm nextgen = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `slot:int`, `st:cm_src_state`),
      cm_state_nextgen_activate_local);
  thm old_le_sum = int_arith_rule(
      `cm_state_nextgen (st:cm_src_state) <=
       cm_state_nextgen st + 1i`);
  thm growth_view = beta_norm(ap_term_rule(
      `\new_limit:int.
         cm_state_nextgen (st:cm_src_state) <= new_limit`,
      nextgen));
  thm growth = eq_mp_rule(sym_rule(growth_view), old_le_sum);
  thm result = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `ks:(cm_frame)list`, `p:cm_program`, `fid:int`,
      `cm_state_nextgen (st:cm_src_state)`,
      `cm_state_nextgen
        (cm_activate_local p fid (slot:int) st)`),
      cm_frames_generation_below_mono), growth), assume_rule(
        `cm_frames_generation_below (p:cm_program) (fid:int)
          (cm_state_nextgen (st:cm_src_state)) (ks:(cm_frame)list)`));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF static thm cm_frames_generation_activate_local =
    cm_prove_frames_generation_activate_local();

PROOF static thm cm_prove_sstart_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (stmt:cm_stmt)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_stmt_static_valid p
           (inth fid (cm_program_functions p)) stmt ==>
         cm_state_generation_below p fid st ==>
         cm_frames_generation_below p fid (cm_state_nextgen st) ks ==>
         cm_task_generation_below p (cm_sstart p fid stmt st ks)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm old_state = assume_rule(
      `cm_state_generation_below (p:cm_program) (fid:int)
        (st:cm_src_state)`);
  thm old_frames = assume_rule(
      `cm_frames_generation_below (p:cm_program) (fid:int)
        (cm_state_nextgen (st:cm_src_state)) (ks:(cm_frame)list)`);
  thm state_open = conv_rule(rewrite_conv(THM_LIST(
      cm_state_generation_below_def)), old_state);
  thm old_env = conjunct1_rule(conjunct2_rule(state_open));
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`stmt:cm_stmt`, get_cm_stmt_cases()), "Hstmt");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hstmt");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hstmt", NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hstmt")].tm);
    thm_list rules = THM_LIST(
        shape, get_cm_sstart_def(), cm_task_generation_below_cond,
        cm_frames_generation_below_cond,
        cm_task_generation_below_def,
        cm_frames_generation_below_def,
        cm_frame_generation_below_def, cm_frame_parent_fid_def,
        cm_control_generation_below_def, old_state, old_frames,
        get_theorem_by_name("COND_ID"));
    if (i == 2 || i == 3) {
      term concrete = rhs_of(shape);
      term slot = cm_ggs_constructor_arg(
          concrete, i == 2 ? 1 : 2, 0);
      thm activated = match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, slot, `st:cm_src_state`),
          cm_state_generation_activate_local), old_state);
      thm frames_grown = match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, slot, `st:cm_src_state`,
          `ks:(cm_frame)list`), cm_frames_generation_activate_local),
          old_frames);
      vector_add(&rules, activated);
      vector_add(&rules, frames_grown);
    } else if (i == 5) {
      vector_add(&rules, old_env);
    }
    thm result = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(branch->g)));
    ACCEPT_TAC(branch, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_sstart_generation_below =
    cm_prove_sstart_generation_below();

PROOF static int cmc_preservation_generation_step_start_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_generation_step_start_axioms_before,
      "cmc_preservation_generation_step_start introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_sstart_generation_below)) == 0,
      "generation-start theorem is not closed");
  return 0;
err:
  return -1;
}

PROOF static int _cmc_preservation_generation_step_start_checks =
    cmc_preservation_generation_step_start_final_checks();
