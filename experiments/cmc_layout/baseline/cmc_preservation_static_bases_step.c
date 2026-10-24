#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_static_bases_step.h"
#include "cmc_preservation_call_value.h"
#include "cmc_preservation_invariant_transition.h"
#include "cmc_preservation_generation.h"

#require "cmc_preservation_static_bases.c"
#require "cmc_preservation_call_value.c"
#require "cmc_preservation_invariant_transition.c"
#require "cmc_preservation_source.c"

PROOF static size_t _cmc_preservation_static_bases_step_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_sbs_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_sbs_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_sbs_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_sbs_consequence(thm source, term consequence) {
  return mp_rule(taut_rule(mk_imp(concl(source), consequence)), source);
}

PROOF static thm cm_prove_bases_below_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:(cm_region)list) (right:(cm_region)list)
         (small:int) (large:int).
         small <= large ==>
         cm_region_bases_below_equal left right large ==>
         cm_region_bases_below_equal left right small`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm bases = conv_rule(rewrite_conv(THM_LIST(
      cm_region_bases_below_equal_def)), assume_rule(
        `cm_region_bases_below_equal
          (left:(cm_region)list) (right:(cm_region)list) (large:int)`));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_region_bases_below_equal_def)));
  gnode with_gen = GEN_TAC(opened, "gen");
  gnode with_bound = DISCH_TAC(with_gen, "Hbound");
  thm large_bound = mp_rule(mp_rule(int_arith_rule(
      `(gen:int) < (small:int) ==> small <= (large:int) ==>
       gen < large`), assume_rule(`(gen:int) < (small:int)`)),
      assume_rule(`(small:int) <= (large:int)`));
  ACCEPT_TAC(with_bound,
      match_mp_rule(spec_rule(`gen:int`, bases), large_bound));
  return gnode_prove(root);
}
PROOF static thm cm_bases_below_mono = cm_prove_bases_below_mono();

PROOF static thm cm_prove_static_bases_transport(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (new_regions:(cm_region)list)
         (old_regions:(cm_region)list) (nextgen:int).
         cm_first_dynamic_generation p <= nextgen ==>
         cm_region_bases_below_equal new_regions old_regions nextgen ==>
         cm_region_bases_below_equal old_regions (cm_static_regions p)
           (cm_first_dynamic_generation p) ==>
         cm_region_bases_below_equal new_regions (cm_static_regions p)
           (cm_first_dynamic_generation p)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm restricted = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `new_regions:(cm_region)list`, `old_regions:(cm_region)list`,
        `cm_first_dynamic_generation (p:cm_program)`, `nextgen:int`),
        cm_bases_below_mono),
      assume_rule(
        `cm_first_dynamic_generation (p:cm_program) <= (nextgen:int)`)),
      assume_rule(
        `cm_region_bases_below_equal
          (new_regions:(cm_region)list) (old_regions:(cm_region)list)
          (nextgen:int)`));
  ACCEPT_TAC(leaf, match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `new_regions:(cm_region)list`, `old_regions:(cm_region)list`,
        `cm_static_regions (p:cm_program)`,
        `cm_first_dynamic_generation p`),
        cm_region_bases_below_equal_trans), restricted), assume_rule(
          `cm_region_bases_below_equal
            (old_regions:(cm_region)list)
            (cm_static_regions (p:cm_program))
            (cm_first_dynamic_generation p)`)));
  return gnode_prove(root);
}
PROOF static thm cm_static_bases_transport =
    cm_prove_static_bases_transport();

PROOF static thm cm_prove_activate_local_static_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (slot:int) (st:cm_src_state).
         cm_state_generation_below p fid st ==>
         cm_region_bases_below_equal
           (cm_state_regions st) (cm_static_regions p)
           (cm_first_dynamic_generation p) ==>
         cm_region_bases_below_equal
           (cm_state_regions (cm_activate_local p fid slot st))
           (cm_static_regions p) (cm_first_dynamic_generation p)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm state_generation = conv_rule(rewrite_conv(THM_LIST(
      cm_state_generation_below_def)), assume_rule(
        `cm_state_generation_below (p:cm_program) (fid:int)
          (st:cm_src_state)`));
  thm lower = conjunct1_rule(state_generation);
  term fresh =
      `CMRegion (cm_state_nextgen (st:cm_src_state))
        (cm_local_base (p:cm_program) (fid:int) (slot:int)
          (cm_state_fp st)) 0i
        (cm_slot_size (cm_program_structs p)
          (inth slot
            (cm_function_locals
              (inth fid (cm_program_functions p))))) T T`;
  thm fresh_rule = specl_rule(TERM_LIST(fresh,
      `cm_state_regions (st:cm_src_state)`,
      `cm_first_dynamic_generation (p:cm_program)`),
      cm_region_bases_fresh_cons);
  fresh_rule = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_region_gen_def())), fresh_rule);
  thm fresh_bases = match_mp_rule(fresh_rule, lower);
  thm combined = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `${fresh:cm_region} :: cm_state_regions (st:cm_src_state)`,
        `cm_state_regions st`, `cm_static_regions (p:cm_program)`,
        `cm_first_dynamic_generation p`),
        cm_region_bases_below_equal_trans), fresh_bases),
      assume_rule(
        `cm_region_bases_below_equal
          (cm_state_regions (st:cm_src_state))
          (cm_static_regions (p:cm_program))
          (cm_first_dynamic_generation p)`));
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_activate_local_def(), get_cm_state_make_def(),
      get_cm_state_regions_def())),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), combined));
  return gnode_prove(root);
}
PROOF static thm cm_activate_local_static_bases =
    cm_prove_activate_local_static_bases();

PROOF static thm cm_prove_enter_call_static_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (callee:int)
         (values:(cm_value)list) (st:cm_src_state).
         cm_state_generation_below p caller st ==>
         cm_region_bases_below_equal
           (cm_state_regions st) (cm_static_regions p)
           (cm_first_dynamic_generation p) ==>
         cm_region_bases_below_equal
           (cm_state_regions (cm_enter_call p callee values st))
           (cm_static_regions p) (cm_first_dynamic_generation p)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm state_generation = conv_rule(rewrite_conv(THM_LIST(
      cm_state_generation_below_def)), assume_rule(
        `cm_state_generation_below (p:cm_program) (caller:int)
          (st:cm_src_state)`));
  thm call_bases = specl_rule(TERM_LIST(
      `p:cm_program`, `callee:int`, `st:cm_src_state`,
      `values:(cm_value)list`), cm_call_regions_bases);
  ACCEPT_TAC(leaf, match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`,
        `cm_state_regions
          (cm_enter_call (p:cm_program) (callee:int)
            (values:(cm_value)list) (st:cm_src_state))`,
        `cm_state_regions st`, `cm_state_nextgen st`),
        cm_static_bases_transport), conjunct1_rule(state_generation)),
      call_bases), assume_rule(
        `cm_region_bases_below_equal
          (cm_state_regions (st:cm_src_state))
          (cm_static_regions (p:cm_program))
          (cm_first_dynamic_generation p)`)));
  return gnode_prove(root);
}
PROOF static thm cm_enter_call_static_bases =
    cm_prove_enter_call_static_bases();

PROOF static thm cm_prove_begin_call_static_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (callee:int)
         (values:(cm_value)list) (st:cm_src_state) (ret:cm_type)
         (ks:(cm_frame)list).
         cm_state_generation_below p caller st ==>
         cm_region_bases_below_equal
           (cm_state_regions st) (cm_static_regions p)
           (cm_first_dynamic_generation p) ==>
         cm_task_static_bases p
           (cm_begin_call p caller callee values st ret ks)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term guard =
      `cm_call_ok (p:cm_program) (callee:int)
        (values:(cm_value)list) (st:cm_src_state) &&
       cm_call_depth (ks:(cm_frame)list) < 65536i`;
  gnode_list cases = BOOL_CASES_TAC(leaf, guard, "Hcall");
  {
    thm entered = match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`, `caller:int`, `callee:int`,
          `values:(cm_value)list`, `st:cm_src_state`),
          cm_enter_call_static_bases), assume_rule(
            `cm_state_generation_below (p:cm_program) (caller:int)
              (st:cm_src_state)`)), assume_rule(
            `cm_region_bases_below_equal
              (cm_state_regions (st:cm_src_state))
              (cm_static_regions (p:cm_program))
              (cm_first_dynamic_generation p)`));
    thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        assume_rule(guard), get_cm_begin_call_def(),
        cm_task_static_bases_def)), goal_ccl(cases[0]->g));
    ACCEPT_TAC(cases[0], eq_mp_rule(sym_rule(target_view), entered));
  }
  {
    thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        assume_rule(mk_not(guard)), get_cm_begin_call_def(),
        cm_task_static_bases_def)), goal_ccl(cases[1]->g));
    ACCEPT_TAC(cases[1], eq_mp_rule(sym_rule(target_view), assume_rule(
        `cm_region_bases_below_equal
          (cm_state_regions (st:cm_src_state))
          (cm_static_regions (p:cm_program))
          (cm_first_dynamic_generation p)`)));
  }
  return gnode_prove(root);
}
PROOF static thm cm_begin_call_static_bases =
    cm_prove_begin_call_static_bases();

PROOF static thm cm_prove_restore_regions_static_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (oldregions:(cm_region)list).
         cm_region_prefix_safe p (cm_state_regions st) fid
           (cm_state_fp st) (cm_state_regions st) oldregions ==>
         cm_region_bases_below_equal
           (cm_state_regions st) (cm_static_regions p)
           (cm_first_dynamic_generation p) ==>
         cm_region_bases_below_equal
           (cm_restore_regions (cm_state_regions st) oldregions)
           (cm_static_regions p) (cm_first_dynamic_generation p)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm equal_bases = match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
        `fid:int`, `cm_state_fp st`, `cm_state_regions st`,
        `oldregions:(cm_region)list`), cm_restore_regions_bases),
      assume_rule(
        `cm_region_prefix_safe (p:cm_program)
          (cm_state_regions (st:cm_src_state)) (fid:int)
          (cm_state_fp st) (cm_state_regions st)
          (oldregions:(cm_region)list)`));
  thm full_bases = conv_rule(rewrite_conv(THM_LIST(
      cm_region_bases_equal_def)), equal_bases);
  thm restricted_body = gen_rule(`gen:int`, disch_rule(
      `(gen:int) < cm_first_dynamic_generation (p:cm_program)`,
      spec_rule(`gen:int`, full_bases)));
  term below_term =
      `cm_region_bases_below_equal
        (cm_restore_regions (cm_state_regions (st:cm_src_state))
          (oldregions:(cm_region)list))
        (cm_state_regions st)
        (cm_first_dynamic_generation (p:cm_program))`;
  thm below_view = apply_conversion(rewrite_conv(THM_LIST(
      cm_region_bases_below_equal_def)), below_term);
  thm below_bases =
      eq_mp_rule(sym_rule(below_view), restricted_body);
  ACCEPT_TAC(leaf, match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_restore_regions (cm_state_regions (st:cm_src_state))
          (oldregions:(cm_region)list)`,
        `cm_state_regions st`, `cm_static_regions (p:cm_program)`,
        `cm_first_dynamic_generation p`),
        cm_region_bases_below_equal_trans), below_bases), assume_rule(
          `cm_region_bases_below_equal
            (cm_state_regions (st:cm_src_state))
            (cm_static_regions (p:cm_program))
            (cm_first_dynamic_generation p)`)));
  return gnode_prove(root);
}
PROOF static thm cm_restore_regions_static_bases =
    cm_prove_restore_regions_static_bases();

PROOF static thm cm_prove_task_static_bases_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (condition:bool)
         (yes:cm_task) (no:cm_task).
         cm_task_static_bases p
           (if condition then yes else no) <=>
         (if condition
          then cm_task_static_bases p yes
          else cm_task_static_bases p no)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      introduced, `condition:bool`, "Hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm branch_result = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          assume_rule(i == 0
            ? `condition:bool`
            : `~(condition:bool)`))),
        goal_ccl(cases[i]->g)));
    ACCEPT_TAC(cases[i], branch_result);
  }
  return gnode_prove(root);
}
PROOF static thm cm_task_static_bases_cond =
    cm_prove_task_static_bases_cond();

PROOF static thm cm_prove_task_static_bases_r_step(void) {
  term task =
      `CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_task_generation_safe p
           (CMRTask p fid expr st ks) (ann:cm_annotation) ==>
         cm_task_static_bases p (CMRTask p fid expr st ks) ==>
         cm_task_static_bases p
           (cm_step (CMRTask p fid expr st ks))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm generation_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_generation_safe_def,
      cm_task_generation_below_def)), assume_rule(
        `cm_task_generation_safe (p:cm_program) ${task:cm_task}
          (ann:cm_annotation)`));
  thm state_generation =
      conjunct1_rule(conjunct1_rule(generation_open));
  thm bases_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_static_bases_def)), assume_rule(
        `cm_task_static_bases (p:cm_program) ${task:cm_task}`));
  thm old_bases = bases_open;
  gnode_list expr_cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hexpr");
  for (size_t i = 0; i < vector_size(expr_cases); ++i) {
    gnode branch = expr_cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hexpr");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hexpr", NULL);
    }
    thm expr_shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hexpr")].tm);
    term concrete = rhs_of(expr_shape);
    if (i == 8) {
      term callee = cm_sbs_constructor_arg(concrete, 3, 0);
      term args = cm_sbs_constructor_arg(concrete, 3, 1);
      term ret = cm_sbs_constructor_arg(concrete, 3, 2);
      gnode_list arg_cases = DISJ_CASES_TAC(branch,
          ispec_rule(args, get_theorem_by_name("list_CASES")),
          "Hargs");
      {
        thm args_nil = assume_rule(
            goal_lasmps(arg_cases[0]->g)[labeled_term_list_index(
              goal_lasmps(arg_cases[0]->g), "Hargs")].tm);
        thm result = match_mp_rule(match_mp_rule(
            specl_rule(TERM_LIST(
              `p:cm_program`, `fid:int`, callee,
              `[]:(cm_value)list`, `st:cm_src_state`, ret,
              `ks:(cm_frame)list`), cm_begin_call_static_bases),
            state_generation), old_bases);
        thm_list rules = THM_LIST(
            expr_shape, args_nil, get_cm_step_def(),
            get_cm_rstart_def(), get_cm_args_start_def());
        result = conv_rule(rewrite_conv(rules), result);
        thm target_view = apply_conversion(rewrite_conv(rules),
            goal_ccl(arg_cases[0]->g));
        ACCEPT_TAC(arg_cases[0],
            eq_mp_rule(sym_rule(target_view), result));
      }
      {
        gnode args_cons =
            ASMP_EXISTS_TAC(arg_cases[1], "Hargs", "arg");
        args_cons = ASMP_EXISTS_TAC(
            args_cons, "Hargs", "tailargs");
        thm args_shape = assume_rule(
            goal_lasmps(args_cons->g)[labeled_term_list_index(
              goal_lasmps(args_cons->g), "Hargs")].tm);
        thm_list rules = THM_LIST(
            expr_shape, args_shape, get_cm_step_def(),
            get_cm_rstart_def(), get_cm_args_start_def(),
            cm_task_static_bases_cond, cm_task_static_bases_def);
        thm result = conv_rule(reduce_rewrite_conv(rules), old_bases);
        thm target_view = apply_conversion(
            reduce_rewrite_conv(rules), goal_ccl(args_cons->g));
        ACCEPT_TAC(args_cons,
            eq_mp_rule(sym_rule(target_view), result));
      }
      continue;
    }
    thm_list rules = THM_LIST(
        expr_shape, get_cm_step_def(), get_cm_rstart_def(),
        get_cm_args_start_def(), cm_task_static_bases_cond,
        cm_task_static_bases_def,
        get_cm_state_io_def(), get_cm_state_make_def(),
        get_cm_state_regions_def(), get_theorem_by_name("COND_ID"));
    thm result = conv_rule(reduce_rewrite_conv(rules), old_bases);
    thm target_view = apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(branch->g));
    ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), result));
  }
  return gnode_prove(root);
}
PROOF static thm cm_task_static_bases_r_step =
    cm_prove_task_static_bases_r_step();

PROOF static thm cm_prove_task_static_bases_l_step(void) {
  term task =
      `CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_task_static_bases p (CMLTask p fid expr st ks) ==>
         cm_task_static_bases p
           (cm_step (CMLTask p fid expr st ks))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm bases_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_static_bases_def)), assume_rule(
        `cm_task_static_bases (p:cm_program) ${task:cm_task}`));
  thm old_bases = bases_open;
  gnode_list expr_cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hexpr");
  for (size_t i = 0; i < vector_size(expr_cases); ++i) {
    gnode branch = expr_cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hexpr");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hexpr", NULL);
    }
    thm expr_shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hexpr")].tm);
    thm_list rules = THM_LIST(
        expr_shape, get_cm_step_def(), get_cm_lstart_def(),
        cm_task_static_bases_cond, cm_task_static_bases_def,
        get_theorem_by_name("COND_ID"));
    thm result = conv_rule(reduce_rewrite_conv(rules), old_bases);
    thm target_view = apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(branch->g));
    ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), result));
  }
  return gnode_prove(root);
}
PROOF static thm cm_task_static_bases_l_step =
    cm_prove_task_static_bases_l_step();

PROOF static thm cm_prove_task_static_bases_s_step(void) {
  term task =
      `CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (stmt:cm_stmt)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_task_generation_safe p
           (CMSTask p fid stmt st ks) (ann:cm_annotation) ==>
         cm_task_static_bases p (CMSTask p fid stmt st ks) ==>
         cm_task_static_bases p
           (cm_step (CMSTask p fid stmt st ks))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm generation_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_generation_safe_def,
      cm_task_generation_below_def)), assume_rule(
        `cm_task_generation_safe (p:cm_program) ${task:cm_task}
          (ann:cm_annotation)`));
  thm state_generation =
      conjunct1_rule(conjunct1_rule(generation_open));
  thm bases_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_static_bases_def)), assume_rule(
        `cm_task_static_bases (p:cm_program) ${task:cm_task}`));
  thm old_bases = bases_open;
  gnode_list stmt_cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`stmt:cm_stmt`, get_datatype_cases("cm_stmt")),
      "Hstmt");
  for (size_t i = 0; i < vector_size(stmt_cases); ++i) {
    gnode branch = stmt_cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hstmt");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hstmt", NULL);
    }
    thm stmt_shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hstmt")].tm);
    term concrete = rhs_of(stmt_shape);
    if (i == 2 || i == 3) {
      term slot = cm_sbs_constructor_arg(concrete,
          i == 2 ? 1 : 2, 0);
      term guard =
          `cm_local_slot_ok (p:cm_program) (fid:int) ${slot:int}`;
      gnode_list local_cases = BOOL_CASES_TAC(branch, guard, "Hlocal");
      {
        thm activated = match_mp_rule(match_mp_rule(
            specl_rule(TERM_LIST(
              `p:cm_program`, `fid:int`, slot, `st:cm_src_state`),
              cm_activate_local_static_bases),
            state_generation), old_bases);
        thm_list rules = THM_LIST(
            stmt_shape, assume_rule(guard), get_cm_step_def(),
            get_cm_sstart_def(), cm_task_static_bases_cond,
            cm_task_static_bases_def);
        thm result = conv_rule(reduce_rewrite_conv(rules), activated);
        thm target_view = apply_conversion(
            reduce_rewrite_conv(rules), goal_ccl(local_cases[0]->g));
        ACCEPT_TAC(local_cases[0],
            eq_mp_rule(sym_rule(target_view), result));
      }
      {
        thm_list rules = THM_LIST(
            stmt_shape, assume_rule(mk_not(guard)), get_cm_step_def(),
            get_cm_sstart_def(), cm_task_static_bases_cond,
            cm_task_static_bases_def);
        thm result = conv_rule(reduce_rewrite_conv(rules), old_bases);
        thm target_view = apply_conversion(
            reduce_rewrite_conv(rules), goal_ccl(local_cases[1]->g));
        ACCEPT_TAC(local_cases[1],
            eq_mp_rule(sym_rule(target_view), result));
      }
      continue;
    }
    thm_list rules = THM_LIST(
        stmt_shape, get_cm_step_def(), get_cm_sstart_def(),
        cm_task_static_bases_cond, cm_task_static_bases_def,
        get_theorem_by_name("COND_ID"));
    thm result = conv_rule(reduce_rewrite_conv(rules), old_bases);
    thm target_view = apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(branch->g));
    ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), result));
  }
  return gnode_prove(root);
}
PROOF static thm cm_task_static_bases_s_step =
    cm_prove_task_static_bases_s_step();

PROOF static thm cm_sbs_successor_not_error(term task) {
  thm not_done = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_task_done_def())),
      mk_not(mk_comb(`cm_task_done`, task))));
  thm next_succeeds = match_mp_rule(match_mp_rule(
      spec_rule(task, cm_task_succeeds_step), not_done),
      assume_rule(mk_comb(`cm_task_succeeds`, task)));
  return match_mp_rule(specl_rule(TERM_LIST(
      `1i:int`, mk_comb(`cm_step`, task)),
      cm_task_succeeds_not_error), next_succeeds);
}

PROOF static thm cm_prove_task_static_bases_v_step(void) {
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_task_generation_safe p
           (CMVTask p fid v st ks) (ann:cm_annotation) ==>
         cm_task_succeeds (CMVTask p fid v st ks) ==>
         cm_task_static_bases p (CMVTask p fid v st ks) ==>
         cm_task_static_bases p
           (cm_step (CMVTask p fid v st ks))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm generation_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_generation_safe_def,
      cm_task_generation_below_def)), assume_rule(
        `cm_task_generation_safe (p:cm_program) ${task:cm_task}
          (ann:cm_annotation)`));
  thm state_generation =
      conjunct1_rule(conjunct1_rule(generation_open));
  thm bases_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_static_bases_def)), assume_rule(
        `cm_task_static_bases (p:cm_program) ${task:cm_task}`));
  thm old_bases = bases_open;
  gnode_list frame_cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`ks:(cm_frame)list`, get_theorem_by_name("list_CASES")),
      "Hframes");
  {
    thm frames_nil = assume_rule(
        goal_lasmps(frame_cases[0]->g)[labeled_term_list_index(
          goal_lasmps(frame_cases[0]->g), "Hframes")].tm);
    thm_list rules = THM_LIST(
        frames_nil, get_cm_step_def(), cm_task_static_bases_cond,
        cm_task_static_bases_def);
    thm result = conv_rule(reduce_rewrite_conv(rules), old_bases);
    thm target_view = apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(frame_cases[0]->g));
    ACCEPT_TAC(frame_cases[0],
        eq_mp_rule(sym_rule(target_view), result));
  }
  gnode cons = ASMP_EXISTS_TAC(frame_cases[1], "Hframes", "head");
  cons = ASMP_EXISTS_TAC(cons, "Hframes", "tail");
  thm frames_cons = assume_rule(
      goal_lasmps(cons->g)[labeled_term_list_index(
        goal_lasmps(cons->g), "Hframes")].tm);
  gnode_list head_cases = DISJ_CASES_TAC(cons,
      ispec_rule(`head:cm_frame`, get_datatype_cases("cm_frame")),
      "Hhead");
  for (size_t i = 0; i < vector_size(head_cases); ++i) {
    gnode branch = head_cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hhead");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hhead", NULL);
    }
    thm head_shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hhead")].tm);
    term concrete = rhs_of(head_shape);
    if (i == 15 || i == 19 || i == 22) {
      thm no_error = cm_sbs_successor_not_error(task);
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          frames_cons, head_shape, get_cm_step_def(),
          get_cm_vapply_def(), cm_error_task_def,
          get_theorem_by_name("NOT_CONS_NIL"),
          get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
          no_error);
      CONTR_TAC(branch, impossible);
      continue;
    }
    if (i == 21) {
      term callee = cm_sbs_constructor_arg(concrete, 4, 0);
      term rest = cm_sbs_constructor_arg(concrete, 4, 1);
      term values = cm_sbs_constructor_arg(concrete, 4, 2);
      term ret = cm_sbs_constructor_arg(concrete, 4, 3);
      gnode_list rest_cases = DISJ_CASES_TAC(branch,
          ispec_rule(rest, get_theorem_by_name("list_CASES")),
          "Hrest");
      {
        thm rest_nil = assume_rule(
            goal_lasmps(rest_cases[0]->g)[labeled_term_list_index(
              goal_lasmps(rest_cases[0]->g), "Hrest")].tm);
        thm entered = match_mp_rule(match_mp_rule(
            specl_rule(TERM_LIST(
              `p:cm_program`, `fid:int`, callee,
              `REVERSE ((v:cm_value) :: ${values:(cm_value)list})`,
              `st:cm_src_state`, ret, `tail:(cm_frame)list`),
              cm_begin_call_static_bases), state_generation), old_bases);
        thm_list rules = THM_LIST(
            frames_cons, head_shape, rest_nil, get_cm_step_def(),
            get_cm_vapply_def(), get_theorem_by_name("NOT_CONS_NIL"),
            get_theorem_by_name("HD"), get_theorem_by_name("TL"));
        thm result = conv_rule(reduce_rewrite_conv(rules), entered);
        thm target_view = apply_conversion(
            reduce_rewrite_conv(rules), goal_ccl(rest_cases[0]->g));
        ACCEPT_TAC(rest_cases[0],
            eq_mp_rule(sym_rule(target_view), result));
      }
      {
        gnode rest_cons =
            ASMP_EXISTS_TAC(rest_cases[1], "Hrest", "nextarg");
        rest_cons = ASMP_EXISTS_TAC(
            rest_cons, "Hrest", "remaining");
        thm rest_shape = assume_rule(
            goal_lasmps(rest_cons->g)[labeled_term_list_index(
              goal_lasmps(rest_cons->g), "Hrest")].tm);
        thm_list rules = THM_LIST(
            frames_cons, head_shape, rest_shape, get_cm_step_def(),
            get_cm_vapply_def(), cm_task_static_bases_cond,
            cm_task_static_bases_def,
            get_theorem_by_name("NOT_CONS_NIL"),
            get_theorem_by_name("HD"), get_theorem_by_name("TL"));
        thm result = conv_rule(reduce_rewrite_conv(rules), old_bases);
        thm target_view = apply_conversion(
            reduce_rewrite_conv(rules), goal_ccl(rest_cons->g));
        ACCEPT_TAC(rest_cons,
            eq_mp_rule(sym_rule(target_view), result));
      }
      continue;
    }
    thm_list rules = THM_LIST(
        frames_cons, head_shape, get_cm_step_def(),
        get_cm_vapply_def(), cm_task_static_bases_cond,
        cm_task_static_bases_def,
        get_cm_state_store_def(), get_cm_state_io_def(),
        get_cm_state_make_def(), get_cm_state_regions_def(),
        get_theorem_by_name("NOT_CONS_NIL"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"),
        get_theorem_by_name("COND_ID"));
    thm result = conv_rule(reduce_rewrite_conv(rules), old_bases);
    thm target_view = apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(branch->g));
    ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), result));
  }
  return gnode_prove(root);
}
PROOF static thm cm_task_static_bases_v_step =
    cm_prove_task_static_bases_v_step();

PROOF static term cm_sbs_runtime_annotation(term phase) {
  return `CMAnnotation (pc:int) (temp:int) (breakpc:int)
    (continuepc:int)
    (CMACursor ${phase:cm_aphase} (owner:int)
       (saved_break:int) (saved_continue:int) ::
     (rest:(cm_acursor)list))
    (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
    (calls:(cm_call_sim_frame)list)`;
}

PROOF static thm_list cm_sbs_annotation_rules(void) {
  return THM_LIST(
      cm_annotation_erases_def,
      cm_ann_cursors_def, cm_cursor_frames_def,
      cm_cursor_phase_def, cm_phase_frame_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"));
}

PROOF static thm cm_sbs_restore_prefix(
    term ann, term phase, term oldregions, thm core) {
  thm opened_core = conv_rule(rewrite_conv(THM_LIST(
      cm_runtime_core_def)), core);
  thm stack = conjunct2_rule(opened_core);
  thm_list rules = THM_LIST(
      cm_ann_cursors_def, cm_cursor_phase_def,
      cm_runtime_stack_def, cm_phase_is_call_def,
      cm_phase_is_scope_def, cm_phase_oldregions_def);
  thm opened_stack = conv_rule(
      reduce_rewrite_conv(rules), stack);
  return cm_sbs_consequence(opened_stack,
      `cm_region_prefix_safe (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        ${oldregions:(cm_region)list}`);
}

PROOF static thm cm_sbs_restore_scope_bases(
    term oldenv, term oldregions, thm prefix, thm old_bases) {
  thm raw = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`, oldregions),
        cm_restore_regions_static_bases), prefix), old_bases);
  term target =
      `cm_region_bases_below_equal
        (cm_state_regions
          (cm_restore_scope (st:cm_src_state)
            ${oldenv:int->int->cm_value}
            ${oldregions:(cm_region)list}))
        (cm_static_regions (p:cm_program))
        (cm_first_dynamic_generation p)`;
  thm target_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_restore_scope_def(), get_cm_state_make_def(),
        get_cm_state_regions_def())), target);
  return eq_mp_rule(sym_rule(target_view), raw);
}

PROOF static thm cm_sbs_restore_call_bases(
    term oldenv, term oldfp, term oldregions,
    thm prefix, thm old_bases) {
  thm raw = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`, oldregions),
        cm_restore_regions_static_bases), prefix), old_bases);
  term target =
      `cm_region_bases_below_equal
        (cm_state_regions
          (cm_restore_call (st:cm_src_state)
            ${oldenv:int->int->cm_value} ${oldfp:int}
            ${oldregions:(cm_region)list}))
        (cm_static_regions (p:cm_program))
        (cm_first_dynamic_generation p)`;
  thm target_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_restore_call_def(), get_cm_state_make_def(),
        get_cm_state_regions_def())), target);
  return eq_mp_rule(sym_rule(target_view), raw);
}

PROOF static thm cm_prove_task_static_bases_c_phase_step(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_sbs_runtime_annotation(phase);
  term task =
      `CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term body = imp_chain(TERM_LIST(
      `cm_annotation_erases ${task:cm_task} ${ann:cm_annotation}`,
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) ${ann:cm_annotation}`,
      `cm_task_static_bases p ${task:cm_task}`),
      `cm_task_static_bases p (cm_step ${task:cm_task})`);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  thm erases = assume_rule(
      `cm_annotation_erases ${task:cm_task} ${ann:cm_annotation}`);
  thm frames_eq = conv_rule(reduce_rewrite_conv(
      cm_sbs_annotation_rules()), erases);
  thm core = assume_rule(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) ${ann:cm_annotation}`);
  thm old_bases = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_static_bases_def)), assume_rule(
        `cm_task_static_bases (p:cm_program) ${task:cm_task}`));
  gnode_list phase_cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(phase, get_datatype_cases("cm_aphase")),
      "Hphase");
  for (size_t i = 0; i < vector_size(phase_cases); ++i) {
    gnode branch = phase_cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hphase", NULL);
    }
    thm phase_shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hphase")].tm);
    term concrete_phase = rhs_of(phase_shape);
    thm concrete_core =
        conv_rule(rewrite_conv(THM_LIST(phase_shape)), core);
    thm result = old_bases;
    thm_list extra = THM_LIST();
    if (i == 15 || i == 19) {
      term oldenv = cm_sbs_constructor_arg(
          concrete_phase, i == 15 ? 4 : 6, i == 15 ? 0 : 2);
      term oldregions = cm_sbs_constructor_arg(
          concrete_phase, i == 15 ? 4 : 6, i == 15 ? 1 : 3);
      thm prefix = cm_sbs_restore_prefix(
          cm_sbs_runtime_annotation(concrete_phase),
          concrete_phase, oldregions, concrete_core);
      result = cm_sbs_restore_scope_bases(
          oldenv, oldregions, prefix, old_bases);
      vector_add(&extra, get_cm_restore_scope_def());
      vector_add(&extra, get_cm_state_make_def());
      vector_add(&extra, get_cm_state_regions_def());
    } else if (i == 22) {
      term oldenv = cm_sbs_constructor_arg(concrete_phase, 5, 1);
      term oldfp = cm_sbs_constructor_arg(concrete_phase, 5, 2);
      term oldregions = cm_sbs_constructor_arg(concrete_phase, 5, 3);
      thm prefix = cm_sbs_restore_prefix(
          cm_sbs_runtime_annotation(concrete_phase),
          concrete_phase, oldregions, concrete_core);
      result = cm_sbs_restore_call_bases(
          oldenv, oldfp, oldregions, prefix, old_bases);
      vector_add(&extra, get_cm_restore_call_def());
      vector_add(&extra, get_cm_state_make_def());
      vector_add(&extra, get_cm_state_regions_def());
    }
    thm_list rules = THM_LIST(
        phase_shape, sym_rule(frames_eq), cm_phase_frame_def,
        get_cm_step_def(), get_cm_capply_def(),
        cm_task_static_bases_cond, cm_task_static_bases_def,
        get_cm_control_kind_def(), get_cm_control_value_def(),
        get_cm_control_status_def(),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"),
        get_theorem_by_name("NOT_CONS_NIL"),
        get_theorem_by_name("COND_ID"));
    for (size_t j = 0; j < vector_size(extra); ++j) {
      vector_add(&rules, extra[j]);
    }
    thm normalized = conv_rule(reduce_rewrite_conv(rules), result);
    thm target_view = apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(branch->g));
    thm resolved = apply_conversion(reduce_rewrite_conv(THM_LIST(
        old_bases, normalized, get_theorem_by_name("COND_ID"))),
        rhs_of(target_view));
    ACCEPT_TAC(branch, eqt_elim_rule(trans_rule(target_view, resolved)));
  }
  return gnode_prove(root);
}
PROOF static thm cm_task_static_bases_c_phase_step =
    cm_prove_task_static_bases_c_phase_step();

PROOF static thm cm_prove_task_static_bases_c_step(void) {
  term task =
      `CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (ctl:cm_control)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_annotation_erases
           (CMCTask p fid ctl st ks) ann ==>
         cm_task_runtime_invariant p
           (CMCTask p fid ctl st ks) ann ==>
         cm_task_static_bases p
           (CMCTask p fid ctl st ks) ==>
         cm_task_static_bases p
           (cm_step (CMCTask p fid ctl st ks))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm runtime_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_runtime_invariant_def, cm_runtime_core_def)),
      assume_rule(
        `cm_task_runtime_invariant (p:cm_program)
          ${task:cm_task} (ann:cm_annotation)`));
  thm core = conv_rule(rewrite_conv(THM_LIST(
      gsym_rule(cm_runtime_core_def))), runtime_open);
  gnode_list ann_cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`ann:cm_annotation`,
        get_datatype_cases("cm_annotation")),
      "Hann");
  gnode branch = ann_cases[0];
  while (true) {
    labeled_term_list assumptions = goal_lasmps(branch->g);
    int index = labeled_term_list_index(assumptions, "Hann");
    if (!is_exists(assumptions[index].tm)) break;
    branch = ASMP_EXISTS_TAC(branch, "Hann", NULL);
  }
  thm ann_shape = assume_rule(
      goal_lasmps(branch->g)[labeled_term_list_index(
        goal_lasmps(branch->g), "Hann")].tm);
  term cursors = cm_sbs_app_arg_from_right(rhs_of(ann_shape), 3);
  gnode_list cursor_cases = DISJ_CASES_TAC(
      branch,
      ispec_rule(cursors, get_theorem_by_name("list_CASES")),
      "Hcursors");
  {
    thm cursors_nil = assume_rule(
        goal_lasmps(cursor_cases[0]->g)[labeled_term_list_index(
          goal_lasmps(cursor_cases[0]->g), "Hcursors")].tm);
    thm shaped_core = conv_rule(rewrite_conv(THM_LIST(
        ann_shape, cursors_nil)), core);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_runtime_core_def, cm_runtime_stack_def,
        cm_ann_cursors_def)), shaped_core);
    CONTR_TAC(cursor_cases[0], impossible);
  }
  gnode cons =
      ASMP_EXISTS_TAC(cursor_cases[1], "Hcursors", "cursor");
  cons = ASMP_EXISTS_TAC(cons, "Hcursors", "cursor_tail");
  thm cursors_cons = assume_rule(
      goal_lasmps(cons->g)[labeled_term_list_index(
        goal_lasmps(cons->g), "Hcursors")].tm);
  gnode_list cursor_shapes = DISJ_CASES_TAC(
      cons,
      ispec_rule(`cursor:cm_acursor`,
        get_datatype_cases("cm_acursor")),
      "Hcursor");
  gnode cursor_branch = cursor_shapes[0];
  while (true) {
    labeled_term_list assumptions = goal_lasmps(cursor_branch->g);
    int index = labeled_term_list_index(assumptions, "Hcursor");
    if (!is_exists(assumptions[index].tm)) break;
    cursor_branch =
        ASMP_EXISTS_TAC(cursor_branch, "Hcursor", NULL);
  }
  thm cursor_shape = assume_rule(
      goal_lasmps(cursor_branch->g)[labeled_term_list_index(
        goal_lasmps(cursor_branch->g), "Hcursor")].tm);
  thm full_shape = conv_rule(rewrite_conv(THM_LIST(
      cursors_cons, cursor_shape)), ann_shape);
  term shaped_ann = rhs_of(full_shape);
  term shaped_cursor = rhs_of(cursor_shape);
  term phase = cm_sbs_constructor_arg(shaped_cursor, 4, 0);
  thm result = specl_rule(TERM_LIST(
      cm_sbs_constructor_arg(shaped_ann, 8, 0),
      cm_sbs_constructor_arg(shaped_ann, 8, 1),
      cm_sbs_constructor_arg(shaped_ann, 8, 2),
      cm_sbs_constructor_arg(shaped_ann, 8, 3),
      phase,
      cm_sbs_constructor_arg(shaped_cursor, 4, 1),
      cm_sbs_constructor_arg(shaped_cursor, 4, 2),
      cm_sbs_constructor_arg(shaped_cursor, 4, 3),
      `cursor_tail:(cm_acursor)list`,
      cm_sbs_constructor_arg(shaped_ann, 8, 5),
      cm_sbs_constructor_arg(shaped_ann, 8, 6),
      cm_sbs_constructor_arg(shaped_ann, 8, 7),
      `p:cm_program`, `fid:int`, `ctl:cm_control`,
      `st:cm_src_state`, `ks:(cm_frame)list`),
      cm_task_static_bases_c_phase_step);
  result = match_mp_rule(result, conv_rule(
      rewrite_conv(THM_LIST(full_shape)), assume_rule(
        `cm_annotation_erases ${task:cm_task}
          (ann:cm_annotation)`)));
  result = match_mp_rule(result,
      conv_rule(rewrite_conv(THM_LIST(full_shape)), core));
  result = match_mp_rule(result, assume_rule(
      `cm_task_static_bases (p:cm_program) ${task:cm_task}`));
  thm target_view = apply_conversion(
      rewrite_conv(THM_LIST(full_shape)),
      goal_ccl(cursor_branch->g));
  ACCEPT_TAC(cursor_branch,
      eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF static thm cm_task_static_bases_c_step =
    cm_prove_task_static_bases_c_step();

PROOF static thm cm_prove_task_static_bases_step(void) {
  term erases =
      `cm_annotation_erases (task:cm_task) (ann:cm_annotation)`;
  term generation =
      `cm_task_generation_safe (root:cm_program)
        (task:cm_task) (ann:cm_annotation)`;
  term runtime =
      `cm_task_runtime_invariant (root:cm_program)
        (task:cm_task) (ann:cm_annotation)`;
  term succeeds = `cm_task_succeeds (task:cm_task)`;
  term bases =
      `cm_task_static_bases (root:cm_program) (task:cm_task)`;
  term target =
      `cm_task_static_bases (root:cm_program)
        (cm_step (task:cm_task))`;
  term body = imp_chain(
      TERM_LIST(erases, generation, runtime, succeeds, bases), target);
  gnode root_node = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root_node);
  gnode_list cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`task:cm_task`, get_datatype_cases("cm_task")),
      "Htask");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Htask");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Htask", NULL);
    }
    thm task_shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Htask")].tm);
    term concrete = rhs_of(task_shape);
    thm result = empty_theorem;
    if (i == 0) {
      term program = cm_sbs_constructor_arg(concrete, 2, 0);
      term input = cm_sbs_constructor_arg(concrete, 2, 1);
      thm program_eq = conv_rule(reduce_rewrite_conv(THM_LIST(
          task_shape, cm_task_static_bases_def)), assume_rule(bases));
      thm initial_generation = specl_rule(
          TERM_LIST(`root:cm_program`, input),
          cm_state_generation_initial);
      thm initial_bases = specl_rule(TERM_LIST(
          `cm_static_regions (root:cm_program)`,
          `cm_first_dynamic_generation (root:cm_program)`),
          cm_region_bases_below_equal_refl);
      initial_bases = conv_rule(rewrite_conv(THM_LIST(
          cm_static_regions_def)), initial_bases);
      thm initial_view = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_initial_state_def(), get_cm_state_make_def(),
            get_cm_state_regions_def(), cm_static_regions_def)),
          `cm_region_bases_below_equal
            (cm_state_regions
              (cm_initial_state (root:cm_program) ${input:(int)list}))
            (cm_static_regions root)
            (cm_first_dynamic_generation root)`);
      thm initial_state_bases =
          eq_mp_rule(sym_rule(initial_view), initial_bases);
      result = specl_rule(TERM_LIST(
          `root:cm_program`, `--1i`,
          `cm_program_main (root:cm_program)`,
          `[]:(cm_value)list`,
          `cm_initial_state (root:cm_program) ${input:(int)list}`,
          `CMIntTy`, `[CMHaltK]`), cm_begin_call_static_bases);
      result = match_mp_rule(result, initial_generation);
      result = match_mp_rule(result, initial_state_bases);
      thm_list rules = THM_LIST(
          task_shape, program_eq, get_cm_step_def());
      result = conv_rule(rewrite_conv(rules), result);
      thm target_view = apply_conversion(
          rewrite_conv(rules), goal_ccl(branch->g));
      ACCEPT_TAC(branch,
          eq_mp_rule(sym_rule(target_view), result));
      continue;
    }
    if (i == 6) {
      thm_list rules = THM_LIST(
          task_shape, get_cm_step_def(), cm_task_static_bases_def);
      result = conv_rule(reduce_rewrite_conv(rules),
          conv_rule(rewrite_conv(THM_LIST(task_shape)),
            assume_rule(bases)));
      thm target_view = apply_conversion(
          reduce_rewrite_conv(rules), goal_ccl(branch->g));
      ACCEPT_TAC(branch,
          eq_mp_rule(sym_rule(target_view), result));
      continue;
    }
    term program = cm_sbs_constructor_arg(concrete, 5, 0);
    term fid = cm_sbs_constructor_arg(concrete, 5, 1);
    term payload = cm_sbs_constructor_arg(concrete, 5, 2);
    term st = cm_sbs_constructor_arg(concrete, 5, 3);
    term frames = cm_sbs_constructor_arg(concrete, 5, 4);
    thm opened_bases = conv_rule(reduce_rewrite_conv(THM_LIST(
        task_shape, cm_task_static_bases_def)), assume_rule(bases));
    thm program_eq = conjunct1_rule(opened_bases);
    thm_list root_rules = THM_LIST(task_shape, program_eq);
    thm shaped_bases =
        conv_rule(rewrite_conv(root_rules), assume_rule(bases));
    if (i == 1) {
      result = specl_rule(TERM_LIST(
          `root:cm_program`, fid, payload, st, frames),
          cm_task_static_bases_r_step);
      result = match_mp_rule(result,
          conv_rule(rewrite_conv(root_rules),
            assume_rule(generation)));
      result = match_mp_rule(result, shaped_bases);
    } else if (i == 2) {
      result = match_mp_rule(specl_rule(TERM_LIST(
          `root:cm_program`, fid, payload, st, frames),
          cm_task_static_bases_l_step), shaped_bases);
    } else if (i == 3) {
      result = specl_rule(TERM_LIST(
          `root:cm_program`, fid, payload, st, frames),
          cm_task_static_bases_s_step);
      result = match_mp_rule(result,
          conv_rule(rewrite_conv(root_rules),
            assume_rule(generation)));
      result = match_mp_rule(result, shaped_bases);
    } else if (i == 4) {
      result = specl_rule(TERM_LIST(
          `root:cm_program`, fid, payload, st, frames),
          cm_task_static_bases_v_step);
      result = match_mp_rule(result,
          conv_rule(rewrite_conv(root_rules),
            assume_rule(generation)));
      result = match_mp_rule(result,
          conv_rule(rewrite_conv(root_rules),
            assume_rule(succeeds)));
      result = match_mp_rule(result, shaped_bases);
    } else {
      result = specl_rule(TERM_LIST(
          `root:cm_program`, fid, payload, st, frames,
          `ann:cm_annotation`), cm_task_static_bases_c_step);
      result = match_mp_rule(result,
          conv_rule(rewrite_conv(root_rules),
            assume_rule(erases)));
      result = match_mp_rule(result,
          conv_rule(rewrite_conv(root_rules),
            assume_rule(runtime)));
      result = match_mp_rule(result, shaped_bases);
    }
    thm_list rules = root_rules;
    result = conv_rule(rewrite_conv(rules), result);
    thm target_view = apply_conversion(
        rewrite_conv(rules), goal_ccl(branch->g));
    ACCEPT_TAC(branch,
        eq_mp_rule(sym_rule(target_view), result));
  }
  return gnode_prove(root_node);
}
PROOF thm cm_task_static_bases_step =
    cm_prove_task_static_bases_step();

PROOF thm get_cm_task_static_bases_step(void) {
  return cm_task_static_bases_step;
}

PROOF static int cmc_preservation_static_bases_step_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_static_bases_step_axioms_before,
      "cmc_preservation_static_bases_step introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_task_static_bases_step)) == 0,
      "static-base step theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_static_bases_step_checks =
    cmc_preservation_static_bases_step_final_checks();
