#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_generation_step_apply.h"
#include "cmc_preservation_generation_step_start.h"
#include "cmc_lang.h"
#include "cmc_preservation_generation.h"
#include "cmc_preservation_generation_state.h"
#include "cmc_preservation_generation_frame.h"

#require "cmc_preservation_generation_step_start.c"

PROOF static size_t _cmc_preservation_generation_step_apply_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_gga_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_gga_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_gga_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_prove_gga_task_generation_cond(void) {
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
PROOF static thm cm_gga_task_generation_cond =
    cm_prove_gga_task_generation_cond();

PROOF static thm cm_prove_gga_frames_generation_cond(void) {
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
PROOF static thm cm_gga_frames_generation_cond =
    cm_prove_gga_frames_generation_cond();

PROOF static thm cm_gga_int_value(term limit, term value) {
  return eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_value_generation_below_def)),
      mk_comb(mk_comb(`cm_value_generation_below`, limit), value)));
}

PROOF static thm cm_prove_state_nextgen_positive(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state).
         cm_state_generation_below p fid st ==>
         0i < cm_state_nextgen st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      cm_state_generation_below_def)), assume_rule(
        `cm_state_generation_below (p:cm_program) (fid:int)
          (st:cm_src_state)`));
  thm globals_nonnegative = ispec_rule(
      `cm_program_globals (p:cm_program)`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  thm strings_nonnegative = ispec_rule(
      `cm_program_strings (p:cm_program)`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  thm expanded_positive = mp_rule(mp_rule(int_arith_rule(
      `0i <= ilength (cm_program_globals (p:cm_program)) ==>
       0i <= ilength (cm_program_strings p) ==>
       0i < 1i + ilength (cm_program_globals p) +
         ilength (cm_program_strings p)`), globals_nonnegative),
      strings_nonnegative);
  thm first_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_first_dynamic_generation_def())),
      `0i < cm_first_dynamic_generation (p:cm_program)`);
  thm first_positive =
      eq_mp_rule(sym_rule(first_view), expanded_positive);
  thm result = mp_rule(mp_rule(int_arith_rule(
      `0i < cm_first_dynamic_generation (p:cm_program) ==>
       cm_first_dynamic_generation p <=
         cm_state_nextgen (st:cm_src_state) ==>
       0i < cm_state_nextgen st`), first_positive),
      conjunct1_rule(opened));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_state_nextgen_positive =
    cm_prove_state_nextgen_positive();

PROOF static thm cm_prove_control_value_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(ctl:cm_control) (limit:int).
         cm_control_generation_below limit ctl ==>
         cm_value_generation_below limit (cm_control_value ctl)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`ctl:cm_control`, get_datatype_cases("cm_control")),
      "Hctl");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hctl");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hctl", NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hctl")].tm);
    thm source = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_control_generation_below_def)), assume_rule(
          `cm_control_generation_below (limit:int) (ctl:cm_control)`));
    thm result = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          shape, cm_control_generation_below_def,
          get_cm_control_value_def(), cm_value_generation_below_def,
          source)),
        goal_ccl(branch->g)));
    ACCEPT_TAC(branch, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_control_value_generation_below =
    cm_prove_control_value_generation_below();

PROOF static thm cm_prove_state_nextgen_restore_scope(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (oldenv:int->int->cm_value)
         (oldregions:(cm_region)list).
         cm_state_nextgen (cm_restore_scope st oldenv oldregions) ==
         cm_state_nextgen st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_restore_scope_def());
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF static thm cm_state_nextgen_restore_scope =
    cm_prove_state_nextgen_restore_scope();

PROOF static thm cm_prove_state_nextgen_restore_call(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (oldenv:int->int->cm_value) (oldfp:int)
         (oldregions:(cm_region)list).
         cm_state_nextgen
          (cm_restore_call st oldenv oldfp oldregions) ==
         cm_state_nextgen st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_restore_call_def());
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF static thm cm_state_nextgen_restore_call =
    cm_prove_state_nextgen_restore_call();

PROOF static thm cm_prove_vapply_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (frame:cm_frame)
         (v:cm_value) (st:cm_src_state) (ks:(cm_frame)list).
         ~(cm_is_call_frame frame) ==>
         cm_state_generation_below p fid st ==>
         cm_value_generation_below (cm_state_nextgen st) v ==>
         cm_frame_generation_below p fid
           (cm_state_nextgen st) frame ==>
         cm_frames_generation_below p
           (cm_frame_parent_fid frame fid)
           (cm_state_nextgen st) ks ==>
         cm_task_generation_below p
           (cm_vapply p fid frame v st ks)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm old_state = assume_rule(
      `cm_state_generation_below (p:cm_program) (fid:int)
        (st:cm_src_state)`);
  thm value_below = assume_rule(
      `cm_value_generation_below (cm_state_nextgen (st:cm_src_state))
        (v:cm_value)`);
  thm frame_source = assume_rule(
      `cm_frame_generation_below (p:cm_program) (fid:int)
        (cm_state_nextgen (st:cm_src_state)) (frame:cm_frame)`);
  thm tail_source = assume_rule(
      `cm_frames_generation_below (p:cm_program)
        (cm_frame_parent_fid (frame:cm_frame) (fid:int))
        (cm_state_nextgen (st:cm_src_state)) (ks:(cm_frame)list)`);
  thm positive = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`),
      cm_state_nextgen_positive), old_state);
  thm state_open = conv_rule(rewrite_conv(THM_LIST(
      cm_state_generation_below_def)), old_state);
  thm old_env = conjunct1_rule(conjunct2_rule(state_open));
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`frame:cm_frame`, get_datatype_cases("cm_frame")),
      "Hframe");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hframe");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hframe", NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hframe")].tm);
    if (i == 22) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, get_cm_is_call_frame_def())), assume_rule(
            `~(cm_is_call_frame (frame:cm_frame))`));
      CONTR_TAC(branch, impossible);
      continue;
    }
    thm frame_below = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_frame_generation_below_def)), frame_source);
    thm tail_below = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_frame_parent_fid_def)), tail_source);
    thm_list rules = THM_LIST(
        shape, get_cm_vapply_def(), cm_gga_task_generation_cond,
        cm_gga_frames_generation_cond,
        cm_task_generation_below_def,
        cm_frames_generation_below_def,
        cm_frame_generation_below_def, cm_frame_parent_fid_def,
        cm_control_generation_below_def, cm_values_generation_below_def,
        old_state, value_below, frame_below, tail_below, old_env,
        positive, get_theorem_by_name("COND_ID"));
    term concrete = rhs_of(shape);
    if (i == 0) {
      thm terminal_state = conj_rule(
          conjunct1_rule(state_open),
          conjunct2_rule(conjunct2_rule(state_open)));
      vector_add(&rules, terminal_state);
    } else if (i == 1) {
      term ty = cm_gga_constructor_arg(concrete, 1, 0);
      thm loaded = match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`, ty,
          `v:cm_value`), cm_load_value_generation_below), old_state);
      vector_add(&rules, loaded);
    } else if (i == 3) {
      term ty = cm_gga_constructor_arg(concrete, 2, 1);
      term ptr = cm_gga_constructor_arg(concrete, 2, 0);
      thm stored = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`, ty, ptr,
          `v:cm_value`), cm_state_generation_store), old_state),
          value_below);
      thm converted = match_mp_rule(specl_rule(TERM_LIST(
          `st:cm_src_state`, ty, `v:cm_value`,
          `cm_state_nextgen (st:cm_src_state)`),
          cm_convert_generation_below), value_below);
      vector_add(&rules, stored);
      vector_add(&rules, converted);
      vector_add(&rules, specl_rule(TERM_LIST(
          ty, ptr, `v:cm_value`, `st:cm_src_state`),
          cm_state_nextgen_store));
    } else if (i == 4) {
      vector_add(&rules, cm_gga_int_value(
          `cm_state_nextgen (st:cm_src_state)`, `CMIntV 1i`));
      vector_add(&rules, cm_gga_int_value(
          `cm_state_nextgen (st:cm_src_state)`, `CMIntV 0i`));
    } else if (i == 5) {
      term op = cm_gga_constructor_arg(concrete, 3, 0);
      term left = cm_gga_constructor_arg(concrete, 3, 1);
      term ty = cm_gga_constructor_arg(concrete, 3, 2);
      thm binary = match_mp_rule(match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(`p:cm_program`, op, left,
            `v:cm_value`, ty, `st:cm_src_state`,
            `cm_state_nextgen (st:cm_src_state)`),
            cm_binary_value_generation_below), positive), frame_below),
          value_below);
      vector_add(&rules, binary);
    } else if (i == 6) {
      term op = cm_gga_constructor_arg(concrete, 1, 0);
      thm unary = specl_rule(TERM_LIST(
          op, `v:cm_value`, `st:cm_src_state`,
          `cm_state_nextgen (st:cm_src_state)`),
          cm_unary_value_generation_below);
      vector_add(&rules, unary);
    } else if (i == 8) {
      term base = cm_gga_constructor_arg(concrete, 2, 0);
      thm shifted = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
          `cm_program_structs (p:cm_program)`, base,
          `cm_value_number (st:cm_src_state) (v:cm_value)`,
          `cm_state_nextgen (st:cm_src_state)`),
          cm_ptr_add_generation_below), positive), frame_below);
      vector_add(&rules, shifted);
    } else if (i == 9) {
      term mid = cm_gga_constructor_arg(concrete, 1, 0);
      thm member = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `v:cm_value`, mid,
          `cm_state_nextgen (st:cm_src_state)`),
          cm_ptr_member_generation_below), positive), value_below);
      vector_add(&rules, member);
    } else if (i == 10 || i == 11) {
      term new_output = i == 10
          ? `(cm_state_output (st:cm_src_state)) ++
              [tower_u8 (cm_value_number st (v:cm_value))]`
          : `(cm_state_output (st:cm_src_state)) ++
              tower_decimal (cm_value_number st (v:cm_value))`;
      thm io_state = match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `cm_state_input (st:cm_src_state)`, new_output),
          cm_state_generation_io), old_state);
      thm io_next = specl_rule(TERM_LIST(
          `st:cm_src_state`, `cm_state_input (st:cm_src_state)`,
          new_output), cm_state_nextgen_io);
      thm output_value = cm_gga_int_value(
          `cm_state_nextgen (st:cm_src_state)`,
          `CMIntV (cm_value_number (st:cm_src_state) (v:cm_value))`);
      vector_add(&rules, io_state);
      vector_add(&rules, io_next);
      vector_add(&rules, output_value);
    } else if (i == 14) {
      term slot = cm_gga_constructor_arg(concrete, 1, 0);
      term ty =
          `cm_slot_ty (inth ${slot:int}
            (cm_function_locals
              (inth (fid:int) (cm_program_functions (p:cm_program)))))`;
      term ptr = `cm_state_env (st:cm_src_state) 1i ${slot:int}`;
      thm stored = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`, ty, ptr,
          `v:cm_value`), cm_state_generation_store), old_state),
          value_below);
      vector_add(&rules, stored);
      vector_add(&rules, specl_rule(TERM_LIST(
          ty, ptr, `v:cm_value`, `st:cm_src_state`),
          cm_state_nextgen_store));
    } else if (i == 15 || i == 19) {
      size_t arity = i == 15 ? 2 : 4;
      term oldenv = cm_gga_constructor_arg(concrete, arity, arity - 2);
      term oldregions = cm_gga_constructor_arg(concrete, arity, arity - 1);
      thm restored = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `fid:int`, `st:cm_src_state`,
          oldenv, oldregions), cm_state_generation_restore_scope),
          old_state), frame_below);
      thm restored_next = specl_rule(TERM_LIST(
          `st:cm_src_state`, oldenv, oldregions),
          cm_state_nextgen_restore_scope);
      vector_add(&rules, restored);
      vector_add(&rules, restored_next);
    } else if (i == 21) {
      term callee = cm_gga_constructor_arg(concrete, 4, 0);
      term values = cm_gga_constructor_arg(concrete, 4, 2);
      term ret = cm_gga_constructor_arg(concrete, 4, 3);
      thm accumulated = eq_mp_rule(sym_rule(apply_conversion(
          rewrite_conv(THM_LIST(cm_values_generation_below_def)),
          `cm_values_generation_below
            (cm_state_nextgen (st:cm_src_state))
            ((v:cm_value) :: ${values:(cm_value)list})`)),
          conj_rule(value_below, frame_below));
      thm reversed = match_mp_rule(specl_rule(TERM_LIST(
          `(v:cm_value) :: ${values:(cm_value)list}`,
          `cm_state_nextgen (st:cm_src_state)`),
          cm_values_generation_below_reverse), accumulated);
      thm begun = match_mp_rule(match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(`p:cm_program`, `fid:int`, callee,
            `REVERSE ((v:cm_value) :: ${values:(cm_value)list})`,
            `st:cm_src_state`, ret, `ks:(cm_frame)list`),
            cm_begin_call_generation_below), old_state), reversed),
          tail_below);
      vector_add(&rules, accumulated);
      vector_add(&rules, reversed);
      vector_add(&rules, begun);
    }
    thm result = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(branch->g)));
    ACCEPT_TAC(branch, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_vapply_generation_below =
    cm_prove_vapply_generation_below();

PROOF static thm cm_prove_capply_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (frame:cm_frame)
         (ctl:cm_control) (st:cm_src_state) (ks:(cm_frame)list).
         cm_state_generation_below p fid st ==>
         cm_control_generation_below (cm_state_nextgen st) ctl ==>
         cm_frame_generation_below p fid
           (cm_state_nextgen st) frame ==>
         cm_frames_generation_below p
           (cm_frame_parent_fid frame fid)
           (cm_state_nextgen st) ks ==>
         cm_task_generation_below p
           (cm_capply p fid frame ctl st ks)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm old_state = assume_rule(
      `cm_state_generation_below (p:cm_program) (fid:int)
        (st:cm_src_state)`);
  thm control_below = assume_rule(
      `cm_control_generation_below
        (cm_state_nextgen (st:cm_src_state)) (ctl:cm_control)`);
  thm state_open = conv_rule(rewrite_conv(THM_LIST(
      cm_state_generation_below_def)), old_state);
  thm frame_source = assume_rule(
      `cm_frame_generation_below (p:cm_program) (fid:int)
        (cm_state_nextgen (st:cm_src_state)) (frame:cm_frame)`);
  thm tail_source = assume_rule(
      `cm_frames_generation_below (p:cm_program)
        (cm_frame_parent_fid (frame:cm_frame) (fid:int))
        (cm_state_nextgen (st:cm_src_state)) (ks:(cm_frame)list)`);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`frame:cm_frame`, get_datatype_cases("cm_frame")),
      "Hframe");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hframe");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hframe", NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hframe")].tm);
    thm frame_below = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_frame_generation_below_def)), frame_source);
    thm tail_below = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_frame_parent_fid_def)), tail_source);
    thm_list rules = THM_LIST(
        shape, get_cm_capply_def(), cm_gga_task_generation_cond,
        cm_gga_frames_generation_cond,
        cm_task_generation_below_def,
        cm_frames_generation_below_def,
        cm_frame_generation_below_def, cm_frame_parent_fid_def,
        cm_control_generation_below_def, cm_values_generation_below_def,
        old_state, control_below, frame_below, tail_below,
        get_theorem_by_name("COND_ID"));
    term concrete = rhs_of(shape);
    if (i == 0) {
      thm terminal_state = conj_rule(
          conjunct1_rule(state_open),
          conjunct2_rule(conjunct2_rule(state_open)));
      vector_add(&rules, terminal_state);
    } else if (i == 15 || i == 19) {
      size_t arity = i == 15 ? 2 : 4;
      term oldenv = cm_gga_constructor_arg(concrete, arity, arity - 2);
      term oldregions = cm_gga_constructor_arg(
          concrete, arity, arity - 1);
      thm restored = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `fid:int`, `st:cm_src_state`,
          oldenv, oldregions), cm_state_generation_restore_scope),
          old_state), frame_below);
      thm restored_next = specl_rule(TERM_LIST(
          `st:cm_src_state`, oldenv, oldregions),
          cm_state_nextgen_restore_scope);
      vector_add(&rules, restored);
      vector_add(&rules, restored_next);
    } else if (i == 22) {
      term caller = cm_gga_constructor_arg(concrete, 5, 0);
      term oldenv = cm_gga_constructor_arg(concrete, 5, 1);
      term oldfp = cm_gga_constructor_arg(concrete, 5, 2);
      term oldregions = cm_gga_constructor_arg(concrete, 5, 3);
      term ret = cm_gga_constructor_arg(concrete, 5, 4);
      term restored_state =
          `cm_restore_call (st:cm_src_state)
            ${oldenv:int->int->cm_value} ${oldfp:int}
            ${oldregions:(cm_region)list}`;
      thm restored = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, caller, `st:cm_src_state`,
          oldenv, oldfp, oldregions), cm_state_generation_restore_call),
          old_state), frame_below);
      thm restored_next = specl_rule(TERM_LIST(
          `st:cm_src_state`, oldenv, oldfp, oldregions),
          cm_state_nextgen_restore_call);
      thm control_value = match_mp_rule(specl_rule(TERM_LIST(
          `ctl:cm_control`, `cm_state_nextgen (st:cm_src_state)`),
          cm_control_value_generation_below), control_below);
      thm converted_return = match_mp_rule(specl_rule(TERM_LIST(
          restored_state, ret, `cm_control_value (ctl:cm_control)`,
          `cm_state_nextgen (st:cm_src_state)`),
          cm_convert_generation_below), control_value);
      thm zero = cm_gga_int_value(
          `cm_state_nextgen (st:cm_src_state)`, `CMIntV 0i`);
      thm converted_zero = match_mp_rule(specl_rule(TERM_LIST(
          restored_state, ret, `CMIntV 0i`,
          `cm_state_nextgen (st:cm_src_state)`),
          cm_convert_generation_below), zero);
      vector_add(&rules, restored);
      vector_add(&rules, restored_next);
      vector_add(&rules, control_value);
      vector_add(&rules, converted_return);
      vector_add(&rules, converted_zero);
    }
    thm result = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(branch->g)));
    ACCEPT_TAC(branch, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_capply_generation_below =
    cm_prove_capply_generation_below();

PROOF static int cmc_preservation_generation_step_apply_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_generation_step_apply_axioms_before,
      "cmc_preservation_generation_step_apply introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_capply_generation_below)) == 0,
      "generation-apply theorem is not closed");
  return 0;
err:
  return -1;
}

PROOF static int _cmc_preservation_generation_step_apply_checks =
    cmc_preservation_generation_step_apply_final_checks();
