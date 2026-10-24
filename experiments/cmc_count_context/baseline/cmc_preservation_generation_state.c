#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_generation_state.h"

#require "cmc_preservation_generation.c"

PROOF static size_t _cmc_preservation_generation_state_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_tags_generation_below_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(tags:int->cm_value) (old:int) (new:int).
         old <= new ==>
         cm_tags_generation_below old tags ==>
         cm_tags_generation_below new tags`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_tags_generation_below_def)));
  gnode point = AUTO_INTROS_TAC(opened);
  thm old_tags = conv_rule(rewrite_conv(THM_LIST(
      cm_tags_generation_below_def)), assume_rule(
        `cm_tags_generation_below (old:int) (tags:int->cm_value)`));
  thm old_value = spec_rule(`addr:int`, old_tags);
  thm result = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `tags (addr:int):cm_value`, `old:int`, `new:int`),
      cm_value_generation_below_mono),
      assume_rule(`(old:int) <= (new:int)`)), old_value);
  ACCEPT_TAC(point, result);
  return gnode_prove(root);
}
PROOF static thm cm_tags_generation_below_mono =
    cm_prove_tags_generation_below_mono();

PROOF static thm cm_prove_env_generation_below_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (env:int->int->cm_value)
         (old:int) (new:int).
         old <= new ==>
         cm_env_generation_below p fid old env ==>
         cm_env_generation_below p fid new env`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_env = conv_rule(rewrite_conv(THM_LIST(
      cm_env_generation_below_def)), assume_rule(
        `cm_env_generation_below (p:cm_program) (fid:int)
          (old:int) (env:int->int->cm_value)`));
  thm old_global = conjunct1_rule(old_env);
  thm old_local_param = conjunct2_rule(old_env);
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_env_generation_below_def)));
  gnode_list top = CONJ_TAC(opened);
  {
    gnode point = AUTO_INTROS_TAC(top[0]);
    thm slot_bounds = assume_rule(
        `0i <= (slot:int) &&
         slot < ilength (cm_program_globals (p:cm_program))`);
    thm old_value = match_mp_rule(
        spec_rule(`slot:int`, old_global), slot_bounds);
    thm result = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `env 0i (slot:int):cm_value`, `old:int`, `new:int`),
        cm_value_generation_below_mono),
        assume_rule(`(old:int) <= (new:int)`)), old_value);
    ACCEPT_TAC(point, result);
  }
  {
    thm old_pair = old_local_param;
    gnode_list pair = CONJ_TAC(top[1]);
    for (size_t scope = 0; scope < 2; ++scope) {
      gnode point = AUTO_INTROS_TAC(pair[scope]);
      thm old_values = scope == 0
          ? conjunct1_rule(old_pair) : conjunct2_rule(old_pair);
      thm slot_bounds = assume_rule(scope == 0
          ? `0i <= (slot:int) &&
             slot < ilength (cm_function_locals
               (inth (fid:int) (cm_program_functions (p:cm_program))))`
          : `0i <= (slot:int) &&
             slot < ilength (cm_function_params
               (inth (fid:int) (cm_program_functions (p:cm_program))))`);
      thm old_value = match_mp_rule(
          spec_rule(`slot:int`, old_values), slot_bounds);
      term value = scope == 0
          ? `env 1i (slot:int):cm_value`
          : `env 2i (slot:int):cm_value`;
      thm result = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
          value, `old:int`, `new:int`), cm_value_generation_below_mono),
          assume_rule(`(old:int) <= (new:int)`)), old_value);
      ACCEPT_TAC(point, result);
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_env_generation_below_mono =
    cm_prove_env_generation_below_mono();

PROOF static thm cm_prove_global_pointer_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (slot:int).
         0i <= slot ==>
         slot < ilength (cm_program_globals p) ==>
         cm_value_generation_below (cm_first_dynamic_generation p)
           (cm_global_pointer p slot)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm strings_nonnegative = ispec_rule(
      `cm_program_strings (p:cm_program)`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  thm bound = mp_rule(mp_rule(mp_rule(int_arith_rule(
      `0i <= ilength (cm_program_strings (p:cm_program)) ==>
       0i <= (slot:int) ==>
       slot < ilength (cm_program_globals p) ==>
       1i + slot < 1i + ilength (cm_program_globals p) +
         ilength (cm_program_strings p)`), strings_nonnegative),
      assume_rule(`0i <= (slot:int)`)), assume_rule(
        `(slot:int) < ilength (cm_program_globals (p:cm_program))`));
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_value_generation_below_def, get_cm_global_pointer_def(),
      get_cm_global_generation_def(),
      get_cm_first_dynamic_generation_def())));
  ACCEPT_TAC(reduced, bound);
  return gnode_prove(root);
}
PROOF thm cm_global_pointer_generation_below =
    cm_prove_global_pointer_generation_below();

PROOF static thm cm_prove_string_pointer_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (slot:int).
         0i <= slot ==>
         slot < ilength (cm_program_strings p) ==>
         cm_value_generation_below (cm_first_dynamic_generation p)
           (cm_string_pointer p slot)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm globals_nonnegative = ispec_rule(
      `cm_program_globals (p:cm_program)`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  thm bound = mp_rule(mp_rule(mp_rule(int_arith_rule(
      `0i <= ilength (cm_program_globals (p:cm_program)) ==>
       0i <= (slot:int) ==>
       slot < ilength (cm_program_strings p) ==>
       1i + ilength (cm_program_globals p) + slot <
         1i + ilength (cm_program_globals p) +
           ilength (cm_program_strings p)`), globals_nonnegative),
      assume_rule(`0i <= (slot:int)`)), assume_rule(
        `(slot:int) < ilength (cm_program_strings (p:cm_program))`));
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_value_generation_below_def, get_cm_string_pointer_def(),
      get_cm_string_generation_def(),
      get_cm_first_dynamic_generation_def())));
  ACCEPT_TAC(reduced, bound);
  return gnode_prove(root);
}
PROOF thm cm_string_pointer_generation_below =
    cm_prove_string_pointer_generation_below();

PROOF static thm cm_prove_state_generation_initial(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         cm_state_generation_below p (--1i) (cm_initial_state p input)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm globals_nonnegative = ispec_rule(
      `cm_program_globals (p:cm_program)`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  thm strings_nonnegative = ispec_rule(
      `cm_program_strings (p:cm_program)`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  thm first_positive = mp_rule(mp_rule(int_arith_rule(
      `0i <= ilength (cm_program_globals (p:cm_program)) ==>
       0i <= ilength (cm_program_strings p) ==>
       0i < 1i + ilength (cm_program_globals p) +
         ilength (cm_program_strings p)`), globals_nonnegative),
      strings_nonnegative);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_initial_state_def());
  vector_add(&rules, cm_state_generation_below_def);
  vector_add(&rules, cm_env_generation_below_def);
  vector_add(&rules, cm_tags_generation_below_def);
  vector_add(&rules, cm_value_generation_below_def);
  vector_add(&rules, get_cm_first_dynamic_generation_def());
  vector_add(&rules, first_positive);
  vector_add(&rules, int_arith_rule(`!(x:int). x <= x`));
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  gnode_list env_parts = CONJ_TAC(opened);
  gnode point = AUTO_INTROS_TAC(env_parts[0]);
  thm slot_bounds = assume_rule(
      `0i <= (slot:int) &&
       slot < ilength (cm_program_globals (p:cm_program))`);
  thm result = specl_rule(TERM_LIST(`p:cm_program`, `slot:int`),
      cm_global_pointer_generation_below);
  result = match_mp_rule(result, conjunct1_rule(slot_bounds));
  result = match_mp_rule(result, conjunct2_rule(slot_bounds));
  thm normalized_result =
      conv_rule(reduce_rewrite_conv(rules), result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(point->g));
  ACCEPT_TAC(point,
      eq_mp_rule(sym_rule(target_view), normalized_result));
  gnode_list null_parts = CONJ_TAC(env_parts[1]);
  for (size_t scope = 0; scope < 2; ++scope) {
    gnode null_value = AUTO_INTROS_TAC(null_parts[scope]);
    thm null_safe = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(cm_value_generation_below_def)),
        goal_ccl(null_value->g)));
    ACCEPT_TAC(null_value, null_safe);
  }
  return gnode_prove(root);
}
PROOF thm cm_state_generation_initial =
    cm_prove_state_generation_initial();

PROOF static thm cm_prove_state_generation_io(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (input:(int)list) (output:(int)list).
         cm_state_generation_below p fid st ==>
         cm_state_generation_below p fid
           (cm_state_io st input output)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old = assume_rule(
      `cm_state_generation_below (p:cm_program) (fid:int)
        (st:cm_src_state)`);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_state_io_def());
  vector_add(&rules, cm_state_generation_below_def);
  thm normalized = conv_rule(reduce_rewrite_conv(rules), old);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}
PROOF thm cm_state_generation_io = cm_prove_state_generation_io();

PROOF static thm cm_prove_tags_generation_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (ty:cm_type) (ptr:cm_value)
         (v:cm_value) (limit:int).
         cm_tags_generation_below limit (cm_state_tags st) ==>
         cm_value_generation_below limit v ==>
         cm_tags_generation_below limit
           (if cm_is_pointer ty
            then (\a:int.
              if a == cm_value_number st ptr
              then cm_convert_value st ty v
              else cm_state_tags st a)
            else cm_state_tags st)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_tags = conv_rule(rewrite_conv(THM_LIST(
      cm_tags_generation_below_def)), assume_rule(
        `cm_tags_generation_below (limit:int)
          (cm_state_tags (st:cm_src_state))`));
  thm converted = match_mp_rule(specl_rule(TERM_LIST(
      `st:cm_src_state`, `ty:cm_type`, `v:cm_value`, `limit:int`),
      cm_convert_generation_below), assume_rule(
        `cm_value_generation_below (limit:int) (v:cm_value)`));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_tags_generation_below_def)));
  gnode point = AUTO_INTROS_TAC(opened);
  gnode_list pointer_cases = BOOL_CASES_TAC(
      point, `cm_is_pointer (ty:cm_type)`, "Hpointer");
  {
    gnode_list address_cases = BOOL_CASES_TAC(pointer_cases[0],
        `(addr:int) == cm_value_number (st:cm_src_state) (ptr:cm_value)`,
        "Haddress");
    CONV_WITH_ASMP_TAC(address_cases[0], reduce_rewrite_conv,
        THM_LIST(converted));
    thm old_value = spec_rule(`addr:int`, old_tags);
    CONV_WITH_ASMP_TAC(address_cases[1], reduce_rewrite_conv,
        THM_LIST(old_value));
  }
  {
    thm old_value = spec_rule(`addr:int`, old_tags);
    CONV_WITH_ASMP_TAC(pointer_cases[1], reduce_rewrite_conv,
        THM_LIST(old_value));
  }
  return gnode_prove(root);
}
PROOF static thm cm_tags_generation_store =
    cm_prove_tags_generation_store();

PROOF static thm cm_prove_state_generation_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ty:cm_type) (ptr:cm_value) (v:cm_value).
         cm_state_generation_below p fid st ==>
         cm_value_generation_below (cm_state_nextgen st) v ==>
         cm_state_generation_below p fid (cm_state_store ty ptr v st)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old = conv_rule(rewrite_conv(THM_LIST(
      cm_state_generation_below_def)), assume_rule(
        `cm_state_generation_below (p:cm_program) (fid:int)
          (st:cm_src_state)`));
  thm tags = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `st:cm_src_state`, `ty:cm_type`, `ptr:cm_value`, `v:cm_value`,
      `cm_state_nextgen (st:cm_src_state)`), cm_tags_generation_store),
      conjunct2_rule(conjunct2_rule(old))), assume_rule(
        `cm_value_generation_below (cm_state_nextgen (st:cm_src_state))
          (v:cm_value)`));
  thm result = conj_rule(conjunct1_rule(old),
      conj_rule(conjunct1_rule(conjunct2_rule(old)), tags));
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_state_store_def());
  vector_add(&rules, cm_state_generation_below_def);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF thm cm_state_generation_store =
    cm_prove_state_generation_store();

PROOF static thm cm_prove_env_generation_update_local(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (env:int->int->cm_value)
         (limit:int) (slot:int) (fresh:cm_value).
         cm_env_generation_below p fid limit env ==>
         cm_value_generation_below limit fresh ==>
         cm_env_generation_below p fid limit
           (\scope:int index:int.
              if scope == 1i && index == slot
              then fresh else env scope index)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_env = conv_rule(rewrite_conv(THM_LIST(
      cm_env_generation_below_def)), assume_rule(
        `cm_env_generation_below (p:cm_program) (fid:int)
          (limit:int) (env:int->int->cm_value)`));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_env_generation_below_def)));
  gnode_list top = CONJ_TAC(opened);
  {
    gnode point = DISCH_TAC(
        GEN_TAC(top[0], "global_index"), "Hglobal_bounds");
    gnode reduced = CONV_TAC(
        point, reduce_rewrite_conv(THM_LIST()));
    gnode bounds = MATCH_MP_TAC(
        reduced, conjunct1_rule(old_env));
    ACCEPT_TAC(bounds, assume_rule(goal_ccl(bounds->g)));
  }
  {
    thm old_pair = conjunct2_rule(old_env);
    gnode_list pair = CONJ_TAC(top[1]);
    {
      gnode point = DISCH_TAC(
          GEN_TAC(pair[0], "local_index"), "Hlocal_bounds");
      gnode_list same = BOOL_CASES_TAC(
          point, `(local_index:int) == (slot:int)`, "Hsame");
      gnode fresh_done = CONV_WITH_ASMP_TAC(
          same[0], reduce_rewrite_conv,
          THM_LIST(assume_rule(
            `cm_value_generation_below (limit:int) (fresh:cm_value)`)));
      if (IS_NULL(fresh_done->solved)) {
        ACCEPT_TAC(fresh_done, assume_rule(goal_ccl(fresh_done->g)));
      }
      gnode old_reduced = CONV_WITH_ASMP_TAC(
          same[1], reduce_rewrite_conv, THM_LIST());
      gnode old_bounds = MATCH_MP_TAC(
          old_reduced, conjunct1_rule(old_pair));
      ACCEPT_TAC(old_bounds, assume_rule(goal_ccl(old_bounds->g)));
    }
    {
      gnode point = DISCH_TAC(
          GEN_TAC(pair[1], "param_index"), "Hparam_bounds");
      gnode reduced = CONV_TAC(
          point, reduce_rewrite_conv(THM_LIST()));
      gnode bounds = MATCH_MP_TAC(
          reduced, conjunct2_rule(old_pair));
      ACCEPT_TAC(bounds, assume_rule(goal_ccl(bounds->g)));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_env_generation_update_local =
    cm_prove_env_generation_update_local();

PROOF static thm cm_prove_state_generation_activate_local(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (slot:int) (st:cm_src_state).
         cm_state_generation_below p fid st ==>
         cm_state_generation_below p fid
           (cm_activate_local p fid slot st)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old = conv_rule(rewrite_conv(THM_LIST(
      cm_state_generation_below_def)), assume_rule(
        `cm_state_generation_below (p:cm_program) (fid:int)
          (st:cm_src_state)`));
  term old_limit = `cm_state_nextgen (st:cm_src_state)`;
  term new_limit = `(cm_state_nextgen (st:cm_src_state)) + 1i`;
  thm grows = int_arith_rule(
      `(cm_state_nextgen (st:cm_src_state)) <=
       cm_state_nextgen st + 1i`);
  thm new_nonnegative = mp_rule(int_arith_rule(
      `cm_first_dynamic_generation (p:cm_program) <=
         cm_state_nextgen (st:cm_src_state) ==>
       cm_first_dynamic_generation p <= cm_state_nextgen st + 1i`),
      conjunct1_rule(old));
  thm grown_env = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `cm_state_env (st:cm_src_state)`,
      old_limit, new_limit), cm_env_generation_below_mono), grows),
      conjunct1_rule(conjunct2_rule(old)));
  term fresh_target =
      `cm_value_generation_below ${new_limit:int}
        (CMPtrV ${old_limit:int} 0i
          (cm_slot_size (cm_program_structs (p:cm_program))
            (inth (slot:int) (cm_function_locals
              (inth (fid:int) (cm_program_functions p)))))
          0i
          (cm_slot_ty
            (inth slot (cm_function_locals
              (inth fid (cm_program_functions p))))))`;
  thm fresh_view = apply_conversion(
      rewrite_conv(THM_LIST(cm_value_generation_below_def)),
      fresh_target);
  struct dest_iff_results fresh_parts = dest_iff(concl(fresh_view));
  thm fresh_below = eq_mp_rule(
      sym_rule(fresh_view), int_arith_rule(fresh_parts.tm2));
  thm updated_env = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `cm_state_env (st:cm_src_state)`,
      new_limit, `slot:int`,
      `CMPtrV ${old_limit:int} 0i
        (cm_slot_size (cm_program_structs (p:cm_program))
          (inth (slot:int) (cm_function_locals
            (inth (fid:int) (cm_program_functions p)))))
        0i
        (cm_slot_ty
          (inth slot (cm_function_locals
            (inth fid (cm_program_functions p))))):cm_value`),
      cm_env_generation_update_local), grown_env), fresh_below);
  thm grown_tags = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_state_tags (st:cm_src_state)`, old_limit, new_limit),
      cm_tags_generation_below_mono), grows),
      conjunct2_rule(conjunct2_rule(old)));
  thm result = conj_rule(new_nonnegative,
      conj_rule(updated_env, grown_tags));
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_activate_local_def());
  vector_add(&rules, cm_state_generation_below_def);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF thm cm_state_generation_activate_local =
    cm_prove_state_generation_activate_local();

PROOF static thm cm_prove_state_generation_restore_scope(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (restore_fid:int)
         (st:cm_src_state) (oldenv:int->int->cm_value)
         (oldregions:(cm_region)list).
         cm_state_generation_below p fid st ==>
         cm_env_generation_below p restore_fid
           (cm_state_nextgen st) oldenv ==>
         cm_state_generation_below p restore_fid
           (cm_restore_scope st oldenv oldregions)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old = conv_rule(rewrite_conv(THM_LIST(
      cm_state_generation_below_def)), assume_rule(
        `cm_state_generation_below (p:cm_program) (fid:int)
          (st:cm_src_state)`));
  thm result = conj_rule(conjunct1_rule(old),
      conj_rule(assume_rule(
        `cm_env_generation_below (p:cm_program) (restore_fid:int)
          (cm_state_nextgen (st:cm_src_state))
          (oldenv:int->int->cm_value)`),
        conjunct2_rule(conjunct2_rule(old))));
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_restore_scope_def());
  vector_add(&rules, cm_state_generation_below_def);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF thm cm_state_generation_restore_scope =
    cm_prove_state_generation_restore_scope();

PROOF static thm cm_prove_state_generation_restore_call(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (caller:int)
         (st:cm_src_state) (oldenv:int->int->cm_value) (oldfp:int)
         (oldregions:(cm_region)list).
         cm_state_generation_below p fid st ==>
         cm_env_generation_below p caller
           (cm_state_nextgen st) oldenv ==>
         cm_state_generation_below p caller
           (cm_restore_call st oldenv oldfp oldregions)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old = conv_rule(rewrite_conv(THM_LIST(
      cm_state_generation_below_def)), assume_rule(
        `cm_state_generation_below (p:cm_program) (fid:int)
          (st:cm_src_state)`));
  thm result = conj_rule(conjunct1_rule(old),
      conj_rule(assume_rule(
        `cm_env_generation_below (p:cm_program) (caller:int)
          (cm_state_nextgen (st:cm_src_state))
          (oldenv:int->int->cm_value)`),
        conjunct2_rule(conjunct2_rule(old))));
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_restore_call_def());
  vector_add(&rules, cm_state_generation_below_def);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF thm cm_state_generation_restore_call =
    cm_prove_state_generation_restore_call();

PROOF static thm cm_prove_call_env_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (fid:int)
         (env:int->int->cm_value) (limit:int) (fp:int).
         cm_env_generation_below p caller limit env ==>
         cm_env_generation_below p fid
           (limit + ilength (cm_function_params
             (inth fid (cm_program_functions p))))
           (cm_call_env p fid env fp limit)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term params =
      `cm_function_params
        (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  term new_limit = `(limit:int) + ilength ${params:(cm_slot_d)list}`;
  thm length_nonnegative = ispec_rule(
      params, get_theorem_by_name("ILENGTH_NONNEG"));
  thm grows = mp_rule(int_arith_rule(
      `0i <= ilength ${params:(cm_slot_d)list} ==>
       (limit:int) <= limit + ilength ${params:(cm_slot_d)list}`),
      length_nonnegative);
  thm grown = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `caller:int`, `env:int->int->cm_value`,
      `limit:int`, new_limit), cm_env_generation_below_mono), grows),
      assume_rule(
        `cm_env_generation_below (p:cm_program) (caller:int)
          (limit:int) (env:int->int->cm_value)`));
  thm grown_open = conv_rule(rewrite_conv(THM_LIST(
      cm_env_generation_below_def)), grown);
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_env_generation_below_def)));
  gnode_list top = CONJ_TAC(opened);
  {
    gnode point = DISCH_TAC(
        GEN_TAC(top[0], "global_index"), "Hglobal_bounds");
    gnode reduced = CONV_TAC(point, reduce_rewrite_conv(THM_LIST(
        get_cm_call_env_def())));
    gnode bounds = MATCH_MP_TAC(
        reduced, conjunct1_rule(grown_open));
    ACCEPT_TAC(bounds, assume_rule(goal_ccl(bounds->g)));
  }
  {
    gnode_list pair = CONJ_TAC(top[1]);
    {
      gnode point = DISCH_TAC(
          GEN_TAC(pair[0], "local_index"), "Hlocal_bounds");
      gnode reduced = CONV_TAC(point, then_conv(
          then_conv(
            rewrite_conv(THM_LIST(get_cm_call_env_def())),
            reduce_rewrite_conv(THM_LIST(
              cm_value_generation_below_def))),
          reduce_rewrite_conv(THM_LIST(
            cm_value_generation_below_def))));
      if (IS_NULL(reduced->solved)) {
        ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
      }
    }
    {
      gnode point = DISCH_TAC(
          GEN_TAC(pair[1], "param_index"), "Hparam_bounds");
      thm bounds = assume_rule(
          `0i <= (param_index:int) &&
           param_index < ilength ${params:(cm_slot_d)list}`);
      thm below = mp_rule(mp_rule(int_arith_rule(
          `0i <= (param_index:int) ==>
           param_index < ilength ${params:(cm_slot_d)list} ==>
           (limit:int) + param_index <
             limit + ilength ${params:(cm_slot_d)list}`),
          conjunct1_rule(bounds)), conjunct2_rule(bounds));
      thm target_view = apply_conversion(
          then_conv(
            rewrite_conv(THM_LIST(get_cm_call_env_def())),
            reduce_rewrite_conv(THM_LIST(
              cm_value_generation_below_def))),
          goal_ccl(point->g));
      struct dest_iff_results call_parts =
          dest_iff(concl(target_view));
      thm pointer_view = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            cm_value_generation_below_def)),
          call_parts.tm2);
      thm pointer_below =
          eq_mp_rule(sym_rule(pointer_view), below);
      ACCEPT_TAC(point,
          eq_mp_rule(sym_rule(target_view), pointer_below));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_call_env_generation_below =
    cm_prove_call_env_generation_below();

PROOF static thm cm_prove_state_generation_call_base(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (fid:int) (st:cm_src_state).
         cm_state_generation_below p caller st ==>
         cm_state_generation_below p fid (cm_call_base_state p fid st)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old = conv_rule(rewrite_conv(THM_LIST(
      cm_state_generation_below_def)), assume_rule(
        `cm_state_generation_below (p:cm_program) (caller:int)
          (st:cm_src_state)`));
  term params =
      `cm_function_params
        (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  term old_limit = `cm_state_nextgen (st:cm_src_state)`;
  term new_limit = `${old_limit:int} + ilength ${params:(cm_slot_d)list}`;
  thm length_nonnegative = ispec_rule(
      params, get_theorem_by_name("ILENGTH_NONNEG"));
  thm grows = mp_rule(int_arith_rule(
      `0i <= ilength ${params:(cm_slot_d)list} ==>
       ${old_limit:int} <= ${new_limit:int}`), length_nonnegative);
  thm new_nonnegative = mp_rule(mp_rule(int_arith_rule(
      `cm_first_dynamic_generation (p:cm_program) <= ${old_limit:int} ==>
       0i <= ilength ${params:(cm_slot_d)list} ==>
       cm_first_dynamic_generation p <= ${new_limit:int}`),
      conjunct1_rule(old)), length_nonnegative);
  thm env = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `caller:int`, `fid:int`,
      `cm_state_env (st:cm_src_state)`, old_limit,
      `cm_state_fp (st:cm_src_state) -
        cm_frame_size (cm_program_structs (p:cm_program))
          (inth (fid:int) (cm_program_functions p))`),
      cm_call_env_generation_below),
      conjunct1_rule(conjunct2_rule(old)));
  thm tags = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_state_tags (st:cm_src_state)`, old_limit, new_limit),
      cm_tags_generation_below_mono), grows),
      conjunct2_rule(conjunct2_rule(old)));
  thm result = conj_rule(new_nonnegative, conj_rule(env, tags));
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_call_base_state_def());
  vector_add(&rules, cm_state_generation_below_def);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF static thm cm_state_generation_call_base =
    cm_prove_state_generation_call_base();

PROOF static thm cm_prove_store_params_generation(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(cm_value)list).
         !(p:cm_program) (fid:int) (index:int) (st:cm_src_state).
           cm_state_generation_below p fid st ==>
           cm_values_generation_below (cm_state_nextgen st) values ==>
           cm_state_generation_below p fid
             (cm_store_params p fid values index st)`);
  gnode_list cases = INDUCT_TAC(root, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_store_params_def())));
    ACCEPT_TAC(reduced, assume_rule(
        `cm_state_generation_below (p:cm_program) (fid:int)
          (st:cm_src_state)`));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm values = conv_rule(rewrite_conv(THM_LIST(
        cm_values_generation_below_def)), assume_rule(
          `cm_values_generation_below
            (cm_state_nextgen (st:cm_src_state))
            ((a0:cm_value) :: (a1:(cm_value)list))`));
    term stored =
        `cm_state_store
          (cm_slot_ty
            (inth (index:int)
              (cm_function_params
                (inth (fid:int)
                  (cm_program_functions (p:cm_program))))))
          (cm_state_env (st:cm_src_state) 2i (index:int))
          (a0:cm_value) st`;
    thm stored_safe = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `cm_slot_ty
          (inth (index:int)
            (cm_function_params
              (inth (fid:int) (cm_program_functions (p:cm_program)))))`,
        `cm_state_env (st:cm_src_state) 2i (index:int)`,
        `a0:cm_value`), cm_state_generation_store), assume_rule(
          `cm_state_generation_below (p:cm_program) (fid:int)
            (st:cm_src_state)`)), conjunct1_rule(values));
    thm tail_below = conjunct2_rule(values);
    thm_list state_rules = get_cm_state_core_defs();
    vector_add(&state_rules, get_cm_state_store_def());
    thm tail_view = apply_conversion(
        reduce_rewrite_conv(state_rules),
        `cm_values_generation_below
          (cm_state_nextgen ${stored:cm_src_state})
          (a1:(cm_value)list)`);
    thm tail_for_stored =
        eq_mp_rule(sym_rule(tail_view), tail_below);
    thm ih = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `(index:int) + 1i`, stored),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    thm result = match_mp_rule(
        match_mp_rule(ih, stored_safe), tail_for_stored);
    thm normalized = conv_rule(rewrite_conv(THM_LIST(
        get_cm_store_params_def())), result);
    thm target_view = apply_conversion(
        rewrite_conv(THM_LIST(get_cm_store_params_def())),
        goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  }
  return gnode_prove(root);
}
PROOF static thm cm_store_params_generation =
    cm_prove_store_params_generation();

PROOF static thm cm_prove_state_generation_enter_call(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (fid:int)
         (values:(cm_value)list) (st:cm_src_state).
         cm_state_generation_below p caller st ==>
         cm_values_generation_below (cm_state_nextgen st) values ==>
         cm_state_generation_below p fid
           (cm_enter_call p fid values st)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term base = `cm_call_base_state
      (p:cm_program) (fid:int) (st:cm_src_state)`;
  thm base_safe = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `caller:int`, `fid:int`, `st:cm_src_state`),
      cm_state_generation_call_base), assume_rule(
        `cm_state_generation_below (p:cm_program) (caller:int)
          (st:cm_src_state)`));
  term params =
      `cm_function_params
        (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  term new_limit =
      `(cm_state_nextgen (st:cm_src_state)) +
       ilength ${params:(cm_slot_d)list}`;
  thm length_nonnegative = ispec_rule(
      params, get_theorem_by_name("ILENGTH_NONNEG"));
  thm grows = mp_rule(int_arith_rule(
      `0i <= ilength ${params:(cm_slot_d)list} ==>
       cm_state_nextgen (st:cm_src_state) <= ${new_limit:int}`),
      length_nonnegative);
  thm values_grown = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `values:(cm_value)list`,
      `cm_state_nextgen (st:cm_src_state)`, new_limit),
      cm_values_generation_below_mono), grows), assume_rule(
        `cm_values_generation_below
          (cm_state_nextgen (st:cm_src_state))
          (values:(cm_value)list)`));
  thm_list base_rules = get_cm_state_core_defs();
  vector_add(&base_rules, get_cm_call_base_state_def());
  thm base_values_view = apply_conversion(
      reduce_rewrite_conv(base_rules),
      `cm_values_generation_below
        (cm_state_nextgen ${base:cm_src_state})
        (values:(cm_value)list)`);
  thm base_values =
      eq_mp_rule(sym_rule(base_values_view), values_grown);
  thm result = specl_rule(TERM_LIST(
      `values:(cm_value)list`, `p:cm_program`, `fid:int`, `0i:int`, base),
      cm_store_params_generation);
  result = match_mp_rule(match_mp_rule(
      result, base_safe), base_values);
  thm normalized = conv_rule(rewrite_conv(THM_LIST(
      get_cm_enter_call_def())), result);
  thm target_view = apply_conversion(
      rewrite_conv(THM_LIST(get_cm_enter_call_def())),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}
PROOF thm cm_state_generation_enter_call =
    cm_prove_state_generation_enter_call();

PROOF static thm cm_prove_load_value_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ty:cm_type) (ptr:cm_value).
         cm_state_generation_below p fid st ==>
         cm_value_generation_below (cm_state_nextgen st)
           (cm_load_value ty ptr st)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old = conv_rule(rewrite_conv(THM_LIST(
      cm_state_generation_below_def)), assume_rule(
        `cm_state_generation_below (p:cm_program) (fid:int)
          (st:cm_src_state)`));
  gnode_list char_cases = BOOL_CASES_TAC(
      leaf, `(ty:cm_type) == CMCharTy`, "Hchar");
  CONV_WITH_ASMP_TAC(char_cases[0], reduce_rewrite_conv, THM_LIST(
      get_cm_load_value_def(), cm_value_generation_below_def));
  gnode_list int_cases = BOOL_CASES_TAC(
      char_cases[1], `(ty:cm_type) == CMIntTy`, "Hint");
  CONV_WITH_ASMP_TAC(int_cases[0], reduce_rewrite_conv, THM_LIST(
      get_cm_load_value_def(), cm_value_generation_below_def));
  gnode_list zero_cases = BOOL_CASES_TAC(int_cases[1],
      `tower_getw (cm_state_mem (st:cm_src_state))
        (cm_value_number st (ptr:cm_value)) == 0i`, "Hzero");
  CONV_WITH_ASMP_TAC(zero_cases[0], reduce_rewrite_conv, THM_LIST(
      get_cm_load_value_def(), cm_value_generation_below_def));
  {
    term address =
        `cm_value_number (st:cm_src_state) (ptr:cm_value)`;
    thm tags = conjunct2_rule(conjunct2_rule(old));
    thm tag = spec_rule(address, conv_rule(rewrite_conv(THM_LIST(
        cm_tags_generation_below_def)), tags));
    thm result = match_mp_rule(specl_rule(TERM_LIST(
        `cm_state_tags (st:cm_src_state) ${address:int}:cm_value`,
        `cm_state_nextgen (st:cm_src_state)`, `ty:cm_type`),
        cm_pointer_retype_generation_below), tag);
    gnode reduced = CONV_WITH_ASMP_TAC(
        zero_cases[1], reduce_rewrite_conv,
        THM_LIST(get_cm_load_value_def()));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_load_value_generation_below =
    cm_prove_load_value_generation_below();

PROOF static conv cm_generation_binary_normalize(thm_list rules) {
  return then_conv(
      then_conv(reduce_rewrite_conv(rules),
        reduce_rewrite_conv(rules)),
      reduce_rewrite_conv(rules));
}

PROOF static thm cm_prove_binary_value_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (op:int) (left:cm_value) (right:cm_value)
         (ty:cm_type) (st:cm_src_state) (limit:int).
         0i < limit ==>
         cm_value_generation_below limit left ==>
         cm_value_generation_below limit right ==>
         cm_value_generation_below limit
           (cm_binary_value p op left right ty st)`);
  gnode current = AUTO_INTROS_TAC(root);
  term_list simple_ops = TERM_LIST(
      `(op:int) == 0i`, `(op:int) == 1i`,
      `(op:int) == 2i`, `(op:int) == 3i`,
      `(op:int) == 4i`, `(op:int) == 5i`,
      `(op:int) == 6i`, `(op:int) == 7i`);
  const char *simple_labels[] = {
    "Hop0", "Hop1", "Hop2", "Hop3",
    "Hop4", "Hop5", "Hop6", "Hop7"
  };
  thm_list rules = THM_LIST(
      get_cm_binary_value_def(), cm_value_generation_below_def);
  thm positive = assume_rule(`0i < (limit:int)`);
  thm left_below = assume_rule(
      `cm_value_generation_below (limit:int) (left:cm_value)`);
  thm right_below = assume_rule(
      `cm_value_generation_below (limit:int) (right:cm_value)`);
  thm left_add = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`, `left:cm_value`,
      `cm_value_number (st:cm_src_state) (right:cm_value)`,
      `limit:int`), cm_ptr_add_generation_below), positive),
      left_below);
  thm right_add = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`, `right:cm_value`,
      `cm_value_number (st:cm_src_state) (left:cm_value)`,
      `limit:int`), cm_ptr_add_generation_below), positive),
      right_below);
  thm left_sub = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`, `left:cm_value`,
      `tower_neg (cm_value_number (st:cm_src_state) (right:cm_value))`,
      `limit:int`), cm_ptr_add_generation_below), positive),
      left_below);
  for (size_t i = 0; i < vector_size(simple_ops); ++i) {
    gnode_list branches = BOOL_CASES_TAC(
        current, simple_ops[i], simple_labels[i]);
    gnode done = CONV_WITH_ASMP_TAC(
        branches[0], cm_generation_binary_normalize, rules);
    if (IS_NULL(done->solved)) {
      ACCEPT_TAC(done, taut_rule(goal_ccl(done->g)));
    }
    current = branches[1];
  }
  gnode_list op8 = BOOL_CASES_TAC(
      current, `(op:int) == 8i`, "Hop8");
  {
    gnode_list left_ptr = BOOL_CASES_TAC(
        op8[0],
        `cm_is_pointer (cm_value_type (left:cm_value))`,
        "Hleft_ptr8");
    gnode left_done = CONV_WITH_ASMP_TAC(
        left_ptr[0], reduce_rewrite_conv,
        THM_LIST(get_cm_binary_value_def()));
    ACCEPT_TAC(left_done, left_add);
    gnode_list right_ptr = BOOL_CASES_TAC(
        left_ptr[1],
        `cm_is_pointer (cm_value_type (right:cm_value))`,
        "Hright_ptr8");
    gnode right_done = CONV_WITH_ASMP_TAC(
        right_ptr[0], reduce_rewrite_conv,
        THM_LIST(get_cm_binary_value_def()));
    ACCEPT_TAC(right_done, right_add);
    gnode scalar_done = CONV_WITH_ASMP_TAC(
        right_ptr[1], cm_generation_binary_normalize, rules);
    if (IS_NULL(scalar_done->solved)) {
      ACCEPT_TAC(scalar_done,
          taut_rule(goal_ccl(scalar_done->g)));
    }
  }
  gnode_list op9 = BOOL_CASES_TAC(
      op8[1], `(op:int) == 9i`, "Hop9");
  {
    gnode_list left_ptr = BOOL_CASES_TAC(
        op9[0],
        `cm_is_pointer (cm_value_type (left:cm_value))`,
        "Hleft_ptr9");
    gnode_list right_ptr = BOOL_CASES_TAC(
        left_ptr[0],
        `cm_is_pointer (cm_value_type (right:cm_value))`,
        "Hright_ptr9");
    gnode both_done = CONV_WITH_ASMP_TAC(
        right_ptr[0], cm_generation_binary_normalize, rules);
    if (IS_NULL(both_done->solved)) {
      ACCEPT_TAC(both_done, taut_rule(goal_ccl(both_done->g)));
    }
    gnode left_sub_done = CONV_WITH_ASMP_TAC(
        right_ptr[1], reduce_rewrite_conv,
        THM_LIST(get_cm_binary_value_def()));
    ACCEPT_TAC(left_sub_done, left_sub);
    gnode scalar_done = CONV_WITH_ASMP_TAC(
        left_ptr[1], cm_generation_binary_normalize, rules);
    if (IS_NULL(scalar_done->solved)) {
      ACCEPT_TAC(scalar_done,
          taut_rule(goal_ccl(scalar_done->g)));
    }
  }
  gnode_list op10 = BOOL_CASES_TAC(
      op9[1], `(op:int) == 10i`, "Hop10");
  gnode ten_done = CONV_WITH_ASMP_TAC(
      op10[0], cm_generation_binary_normalize, rules);
  if (IS_NULL(ten_done->solved)) {
    ACCEPT_TAC(ten_done, taut_rule(goal_ccl(ten_done->g)));
  }
  gnode_list op11 = BOOL_CASES_TAC(
      op10[1], `(op:int) == 11i`, "Hop11");
  for (size_t i = 0; i < vector_size(op11); ++i) {
    gnode done = CONV_WITH_ASMP_TAC(
        op11[i], cm_generation_binary_normalize, rules);
    if (IS_NULL(done->solved)) {
      ACCEPT_TAC(done, taut_rule(goal_ccl(done->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_binary_value_generation_below =
    cm_prove_binary_value_generation_below();

PROOF static thm cm_prove_unary_value_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(op:int) (arg:cm_value) (st:cm_src_state) (limit:int).
         cm_value_generation_below limit
           (cm_unary_value op arg st)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list op_zero = BOOL_CASES_TAC(
      leaf, `(op:int) == 0i`, "Hop_zero");
  thm_list rules = THM_LIST(
      get_cm_unary_value_def(), cm_value_generation_below_def);
  for (size_t i = 0; i < vector_size(op_zero); ++i) {
    gnode reduced = CONV_WITH_ASMP_TAC(
        op_zero[i], cm_generation_binary_normalize, rules);
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_unary_value_generation_below =
    cm_prove_unary_value_generation_below();

PROOF thm get_cm_state_generation_initial(void) {
  return cm_state_generation_initial;
}
PROOF thm get_cm_state_generation_store(void) {
  return cm_state_generation_store;
}
PROOF thm get_cm_state_generation_activate_local(void) {
  return cm_state_generation_activate_local;
}
PROOF thm get_cm_state_generation_enter_call(void) {
  return cm_state_generation_enter_call;
}
PROOF thm get_cm_load_value_generation_below(void) {
  return cm_load_value_generation_below;
}
PROOF thm get_cm_binary_value_generation_below(void) {
  return cm_binary_value_generation_below;
}
PROOF thm get_cm_env_generation_below_mono(void) {
  return cm_env_generation_below_mono;
}

PROOF static int cmc_preservation_generation_state_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_generation_state_axioms_before,
      "cmc_preservation_generation_state introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_generation_state_checks =
    cmc_preservation_generation_state_final_checks();
