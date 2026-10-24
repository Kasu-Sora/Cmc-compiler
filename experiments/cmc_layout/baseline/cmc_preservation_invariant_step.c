#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_invariant.h"
#require "cmc_preservation_invariant.c"
#include "cmc_preservation_code_task.h"
#require "cmc_preservation_code_task.c"
#include "cmc_preservation_invariant_step.h"

PROOF static size_t _cmc_preservation_invariant_step_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_task_runtime_initial(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         cm_task_runtime_invariant p (CMStartTask p input)
           cm_initial_annotation`);
  CONV_TAC(root, reduce_rewrite_conv(THM_LIST(
      cm_task_runtime_invariant_def)));
  return gnode_prove(root);
}
PROOF thm cm_task_runtime_initial =
    cm_prove_task_runtime_initial();

PROOF static thm cm_invariant_step_consequence(
    const thm premise, const term conclusion) {
  return mp_rule(taut_rule(mk_imp(concl(premise), conclusion)),
      premise);
}


PROOF static thm cm_invariant_step_assumption(
    const gnode leaf, const term wanted) {
  labeled_term_list assumptions = goal_lasmps(leaf->g);
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    if (alpha_compare(assumptions[i].tm, wanted) == 0) {
      return assume_rule(assumptions[i].tm);
    }
  }
  ENSURE_COND(false,
      "required invariant-step assumption is absent: %s in %s",
      cstr_term(wanted), cstr_gnode(leaf));
err:
  return empty_theorem;
}
PROOF thm cm_region_bases_equal_def = new_fun_definition(
    `cm_region_bases_equal (left:(cm_region)list)
       (right:(cm_region)list) : bool =
       (!gen.
          cm_region_base left gen == cm_region_base right gen)`);

PROOF static thm cm_prove_region_dead_prefix_refl(void) {
  gnode root = gnode_new_with_ccl(
      `!(regions:(cm_region)list).
         cm_region_dead_prefix regions regions`);
  gnode_list cases = INDUCT_TAC(root, `regions:(cm_region)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_TAC(cases[i], reduce_rewrite_conv(THM_LIST(
        cm_region_dead_prefix_def)));
  }
  return gnode_prove(root);
}
PROOF thm cm_region_dead_prefix_refl =
    cm_prove_region_dead_prefix_refl();

PROOF static thm cm_prove_region_dead_prefix_cons(void) {
  gnode root = gnode_new_with_ccl(
      `!(region:cm_region) (rest:(cm_region)list)
         (old:(cm_region)list).
         ~cm_region_live region ==>
         cm_region_dead_prefix rest old ==>
         cm_region_dead_prefix (region :: rest) old`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list boundary_cases = BOOL_CASES_TAC(
      leaf,
      `(region:cm_region) :: (rest:(cm_region)list) ==
         (old:(cm_region)list)`,
      "Hboundary");
  for (size_t i = 0; i < vector_size(boundary_cases); ++i) {
    CONV_WITH_ASMP_TAC(boundary_cases[i], reduce_rewrite_conv,
        THM_LIST(cm_region_dead_prefix_def));
  }
  return gnode_prove(root);
}
PROOF thm cm_region_dead_prefix_cons =
    cm_prove_region_dead_prefix_cons();

PROOF static thm cm_prove_region_prefix_dead_cons(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (fid:int) (fp:int) (region:cm_region)
         (rest:(cm_region)list) (old:(cm_region)list).
         ~cm_region_live region ==>
         cm_region_prefix_safe p all_regions fid fp rest old ==>
         cm_region_prefix_safe p all_regions fid fp
           (region :: rest) old`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list boundary_cases = BOOL_CASES_TAC(
      leaf,
      `(region:cm_region) :: (rest:(cm_region)list) ==
         (old:(cm_region)list)`,
      "Hboundary");
  for (size_t i = 0; i < vector_size(boundary_cases); ++i) {
    CONV_WITH_ASMP_TAC(boundary_cases[i], reduce_rewrite_conv,
        THM_LIST(cm_region_prefix_safe_def,
          cm_region_frame_safe_def));
  }
  return gnode_prove(root);
}
PROOF thm cm_region_prefix_dead_cons =
    cm_prove_region_prefix_dead_cons();

PROOF static thm cm_prove_region_dead_prefix_trans(void) {
  gnode root = gnode_new_with_ccl(
      `!(outer:(cm_region)list) (middle:(cm_region)list)
         (inner:(cm_region)list).
         cm_region_dead_prefix outer middle ==>
         cm_region_dead_prefix middle inner ==>
         cm_region_dead_prefix outer inner`);
  gnode with_outer = GEN_TAC(root, "outer");
  gnode_list cases =
      INDUCT_TAC(with_outer, `outer:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm outer = conv_rule(rewrite_conv(THM_LIST(
        cm_region_dead_prefix_def)), assume_rule(
          `cm_region_dead_prefix ([]:(cm_region)list)
            (middle:(cm_region)list)`));
    thm middle_nil = outer;
    ACCEPT_TAC(leaf, conv_rule(rewrite_conv(THM_LIST(middle_nil)),
        assume_rule(
          `cm_region_dead_prefix (middle:(cm_region)list)
            (inner:(cm_region)list)`)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list boundary_cases = BOOL_CASES_TAC(
        leaf,
        `(a0:cm_region) :: (a1:(cm_region)list) ==
           (middle:(cm_region)list)`,
        "Hboundary");
    {
      thm boundary = assume_rule(
          `(a0:cm_region) :: (a1:(cm_region)list) ==
             (middle:(cm_region)list)`);
      ACCEPT_TAC(boundary_cases[0],
          conv_rule(rewrite_conv(THM_LIST(sym_rule(boundary))),
            assume_rule(
              `cm_region_dead_prefix (middle:(cm_region)list)
                (inner:(cm_region)list)`)));
    }
    {
      thm not_boundary = assume_rule(
          `~((a0:cm_region) :: (a1:(cm_region)list) ==
              (middle:(cm_region)list))`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_region_dead_prefix_def, not_boundary)), assume_rule(
            `cm_region_dead_prefix
              ((a0:cm_region) :: (a1:(cm_region)list))
              (middle:(cm_region)list)`));
      thm ih = specl_rule(TERM_LIST(
          `middle:(cm_region)list`, `inner:(cm_region)list`),
          assume_rule(goal_lasmps(boundary_cases[1]->g)[0].tm));
      thm tail = match_mp_rule(match_mp_rule(
          ih, conjunct2_rule(opened)),
          assume_rule(
            `cm_region_dead_prefix (middle:(cm_region)list)
              (inner:(cm_region)list)`));
      thm result = match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `a0:cm_region`, `a1:(cm_region)list`,
            `inner:(cm_region)list`),
            cm_region_dead_prefix_cons),
          conjunct1_rule(opened)), tail);
      ACCEPT_TAC(boundary_cases[1], result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_region_dead_prefix_trans =
    cm_prove_region_dead_prefix_trans();

PROOF static thm cm_prove_region_dead_prefix_safe_trans(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (fid:int) (fp:int) (outer:(cm_region)list)
         (middle:(cm_region)list) (inner:(cm_region)list).
         cm_region_dead_prefix outer middle ==>
         cm_region_prefix_safe p all_regions fid fp middle inner ==>
         cm_region_prefix_safe p all_regions fid fp outer inner`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_all = GEN_TAC(with_program, "all_regions");
  gnode with_fid = GEN_TAC(with_all, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode_list cases =
      INDUCT_TAC(with_fp, `outer:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm outer = conv_rule(rewrite_conv(THM_LIST(
        cm_region_dead_prefix_def)), assume_rule(
          `cm_region_dead_prefix ([]:(cm_region)list)
            (middle:(cm_region)list)`));
    thm middle_nil = outer;
    ACCEPT_TAC(leaf, conv_rule(rewrite_conv(THM_LIST(middle_nil)),
        assume_rule(
          `cm_region_prefix_safe (p:cm_program)
            (all_regions:(cm_region)list) (fid:int) (fp:int)
            (middle:(cm_region)list) (inner:(cm_region)list)`)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list boundary_cases = BOOL_CASES_TAC(
        leaf,
        `(a0:cm_region) :: (a1:(cm_region)list) ==
           (middle:(cm_region)list)`,
        "Hboundary");
    {
      thm boundary = assume_rule(
          `(a0:cm_region) :: (a1:(cm_region)list) ==
             (middle:(cm_region)list)`);
      ACCEPT_TAC(boundary_cases[0],
          conv_rule(rewrite_conv(THM_LIST(sym_rule(boundary))),
            assume_rule(
              `cm_region_prefix_safe (p:cm_program)
                (all_regions:(cm_region)list) (fid:int) (fp:int)
                (middle:(cm_region)list) (inner:(cm_region)list)`)));
    }
    {
      thm not_boundary = assume_rule(
          `~((a0:cm_region) :: (a1:(cm_region)list) ==
              (middle:(cm_region)list))`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_region_dead_prefix_def, not_boundary)), assume_rule(
            `cm_region_dead_prefix
              ((a0:cm_region) :: (a1:(cm_region)list))
              (middle:(cm_region)list)`));
      thm ih = specl_rule(TERM_LIST(
          `middle:(cm_region)list`, `inner:(cm_region)list`),
          assume_rule(goal_lasmps(boundary_cases[1]->g)[0].tm));
      thm tail = match_mp_rule(match_mp_rule(
          ih, conjunct2_rule(opened)),
          assume_rule(
            `cm_region_prefix_safe (p:cm_program)
              (all_regions:(cm_region)list) (fid:int) (fp:int)
              (middle:(cm_region)list) (inner:(cm_region)list)`));
      thm result = match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `p:cm_program`, `all_regions:(cm_region)list`,
            `fid:int`, `fp:int`, `a0:cm_region`,
            `a1:(cm_region)list`, `inner:(cm_region)list`),
            cm_region_prefix_dead_cons),
          conjunct1_rule(opened)), tail);
      ACCEPT_TAC(boundary_cases[1], result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_region_dead_prefix_safe_trans =
    cm_prove_region_dead_prefix_safe_trans();

PROOF static thm cm_prove_retire_region_dead(void) {
  gnode root = gnode_new_with_ccl(
      `!(region:cm_region).
         ~cm_region_live (cm_retire_region region)`);
  gnode_list cases = INDUCT_TAC(root, `region:cm_region`);
  thm_list rules = get_cm_runtime_defs();
  vector_add(&rules, get_cm_retire_region_def());
  CONV_TAC(cases[0], reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF thm cm_retire_region_dead =
    cm_prove_retire_region_dead();

PROOF static thm cm_prove_restore_regions_dead_prefix(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (fid:int) (fp:int) (active:(cm_region)list)
         (old:(cm_region)list).
         cm_region_prefix_safe p all_regions fid fp active old ==>
         cm_region_dead_prefix
           (cm_restore_regions active old) old`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_all = GEN_TAC(with_program, "all_regions");
  gnode with_fid = GEN_TAC(with_all, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode_list cases =
      INDUCT_TAC(with_fp, `active:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(
        THM_LIST(get_cm_restore_regions_def())));
    ACCEPT_TAC(reduced,
        spec_rule(`old:(cm_region)list`,
          cm_region_dead_prefix_refl));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list boundary_cases = BOOL_CASES_TAC(
        leaf,
        `(a0:cm_region) :: (a1:(cm_region)list) ==
           (old:(cm_region)list)`,
        "Hboundary");
    {
      gnode reduced = CONV_WITH_ASMP_TAC(
          boundary_cases[0], reduce_rewrite_conv,
          THM_LIST(get_cm_restore_regions_def()));
      ACCEPT_TAC(reduced,
          spec_rule(`old:(cm_region)list`,
            cm_region_dead_prefix_refl));
    }
    {
      thm not_boundary = assume_rule(
          `~((a0:cm_region) :: (a1:(cm_region)list) ==
              (old:(cm_region)list))`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_region_prefix_safe_def, not_boundary)), assume_rule(
            `cm_region_prefix_safe (p:cm_program)
              (all_regions:(cm_region)list) (fid:int) (fp:int)
              ((a0:cm_region) :: (a1:(cm_region)list))
              (old:(cm_region)list)`));
      thm ih = specl_rule(TERM_LIST(
          `old:(cm_region)list`),
          assume_rule(goal_lasmps(boundary_cases[1]->g)[0].tm));
      thm tail = match_mp_rule(ih, conjunct2_rule(opened));
      thm retired_dead =
          spec_rule(`a0:cm_region`, cm_retire_region_dead);
      thm result = match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `cm_retire_region (a0:cm_region)`,
            `cm_restore_regions (a1:(cm_region)list)
              (old:(cm_region)list)`,
            `old:(cm_region)list`),
            cm_region_dead_prefix_cons),
          retired_dead), tail);
      gnode reduced = CONV_WITH_ASMP_TAC(
          boundary_cases[1], reduce_rewrite_conv,
          THM_LIST(get_cm_restore_regions_def(), not_boundary));
      ACCEPT_TAC(reduced, result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_restore_regions_dead_prefix =
    cm_prove_restore_regions_dead_prefix();

PROOF static thm cm_prove_region_base_retire_cons(void) {
  gnode root = gnode_new_with_ccl(
      `!(region:cm_region) (rest:(cm_region)list) (gen:int).
         cm_region_base (cm_retire_region region :: rest) gen ==
         cm_region_base (region :: rest) gen`);
  gnode_list cases = INDUCT_TAC(root, `region:cm_region`);
  gnode leaf = AUTO_INTROS_TAC(cases[0]);
  thm_list rules = get_cm_runtime_defs();
  vector_add(&rules, get_cm_retire_region_def());
  vector_add(&rules, get_cm_region_base_def());
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF thm cm_region_base_retire_cons =
    cm_prove_region_base_retire_cons();


PROOF static thm cm_prove_retire_region_gen(void) {
  gnode root = gnode_new_with_ccl(
      `!(region:cm_region).
         cm_region_gen (cm_retire_region region) ==
         cm_region_gen region`);
  gnode_list cases = INDUCT_TAC(root, `region:cm_region`);
  gnode leaf = AUTO_INTROS_TAC(cases[0]);
  thm_list rules = get_cm_runtime_defs();
  vector_add(&rules, get_cm_retire_region_def());
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF thm cm_retire_region_gen =
    cm_prove_retire_region_gen();
PROOF static thm cm_prove_restore_regions_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (fid:int) (fp:int) (active:(cm_region)list)
         (old:(cm_region)list).
         cm_region_prefix_safe p all_regions fid fp active old ==>
         cm_region_bases_equal
           (cm_restore_regions active old) active`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_all = GEN_TAC(with_program, "all_regions");
  gnode with_fid = GEN_TAC(with_all, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode_list cases =
      INDUCT_TAC(with_fp, `active:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm prefix = conv_rule(rewrite_conv(THM_LIST(
        cm_region_prefix_safe_def)), assume_rule(
          `cm_region_prefix_safe (p:cm_program)
            (all_regions:(cm_region)list) (fid:int) (fp:int)
            ([]:(cm_region)list) (old:(cm_region)list)`));
    gnode opened_goal = CONV_TAC(leaf,
        rewrite_conv(THM_LIST(cm_region_bases_equal_def)));
    gnode with_gen = GEN_TAC(opened_goal, "gen");
    gnode reduced = CONV_WITH_ASMP_TAC(
        with_gen, reduce_rewrite_conv,
        THM_LIST(get_cm_restore_regions_def(), prefix,
          get_cm_region_base_def()));
    if (IS_NULL(reduced->solved)) {
      struct dest_eq_results sides = dest_eq(goal_ccl(reduced->g));
      ACCEPT_TAC(reduced, refl_rule(sides.tm1));
    }
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list boundary_cases = BOOL_CASES_TAC(
        leaf,
        `(a0:cm_region) :: (a1:(cm_region)list) ==
           (old:(cm_region)list)`,
        "Hboundary");
    {
      thm boundary = assume_rule(
          `(a0:cm_region) :: (a1:(cm_region)list) ==
             (old:(cm_region)list)`);
      gnode opened_goal = CONV_TAC(boundary_cases[0],
          rewrite_conv(THM_LIST(cm_region_bases_equal_def)));
      gnode with_gen = GEN_TAC(opened_goal, "gen");
      gnode reduced = CONV_WITH_ASMP_TAC(
          with_gen, reduce_rewrite_conv,
          THM_LIST(get_cm_restore_regions_def(), boundary));
      if (IS_NULL(reduced->solved)) {
        struct dest_eq_results sides = dest_eq(goal_ccl(reduced->g));
        ACCEPT_TAC(reduced, refl_rule(sides.tm1));
      }
    }
    {
      thm not_boundary = assume_rule(
          `~((a0:cm_region) :: (a1:(cm_region)list) ==
              (old:(cm_region)list))`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_region_prefix_safe_def, not_boundary)), assume_rule(
            `cm_region_prefix_safe (p:cm_program)
              (all_regions:(cm_region)list) (fid:int) (fp:int)
              ((a0:cm_region) :: (a1:(cm_region)list))
              (old:(cm_region)list)`));
      thm ih = specl_rule(TERM_LIST(
          `old:(cm_region)list`),
          assume_rule(goal_lasmps(boundary_cases[1]->g)[0].tm));
      thm tail_bases = match_mp_rule(ih, conjunct2_rule(opened));
      gnode opened_goal = CONV_TAC(boundary_cases[1],
          rewrite_conv(THM_LIST(cm_region_bases_equal_def)));
      gnode with_gen = GEN_TAC(opened_goal, "gen");
      thm tail_gen = spec_rule(`gen:int`,
          conv_rule(rewrite_conv(THM_LIST(
            cm_region_bases_equal_def)), tail_bases));
      gnode reduced = CONV_WITH_ASMP_TAC(
          with_gen, reduce_rewrite_conv,
          THM_LIST(get_cm_restore_regions_def(), not_boundary,
            get_cm_region_base_def(), cm_region_base_retire_cons,
            tail_gen));
      if (IS_NULL(reduced->solved)) {
        struct dest_eq_results sides = dest_eq(goal_ccl(reduced->g));
        ACCEPT_TAC(reduced, refl_rule(sides.tm1));
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_restore_regions_bases =
    cm_prove_restore_regions_bases();

PROOF static thm cm_prove_region_frame_safe_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (new_regions:(cm_region)list)
         (old_regions:(cm_region)list) (fid:int) (fp:int)
         (region:cm_region).
         cm_region_bases_equal new_regions old_regions ==>
         cm_region_frame_safe p old_regions fid fp region ==>
         cm_region_frame_safe p new_regions fid fp region`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm bases = conv_rule(rewrite_conv(THM_LIST(
      cm_region_bases_equal_def)), assume_rule(
        `cm_region_bases_equal
          (new_regions:(cm_region)list)
          (old_regions:(cm_region)list)`));
  thm base_equal = spec_rule(
      `cm_region_gen (region:cm_region)`, bases);
  thm old_safe = conv_rule(rewrite_conv(THM_LIST(
      cm_region_frame_safe_def)), assume_rule(
        `cm_region_frame_safe (p:cm_program)
          (old_regions:(cm_region)list) (fid:int) (fp:int)
          (region:cm_region)`));
  thm new_safe = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(base_equal))), old_safe);
  gnode reduced = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_region_frame_safe_def)));
  ACCEPT_TAC(reduced, new_safe);
  return gnode_prove(root);
}
PROOF thm cm_region_frame_safe_bases =
    cm_prove_region_frame_safe_bases();

PROOF static thm cm_prove_region_prefix_safe_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (new_regions:(cm_region)list)
         (old_regions:(cm_region)list) (fid:int) (fp:int)
         (active:(cm_region)list) (old:(cm_region)list).
         cm_region_bases_equal new_regions old_regions ==>
         cm_region_prefix_safe p old_regions fid fp active old ==>
         cm_region_prefix_safe p new_regions fid fp active old`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_new = GEN_TAC(with_program, "new_regions");
  gnode with_old_regions = GEN_TAC(with_new, "old_regions");
  gnode with_fid = GEN_TAC(with_old_regions, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode_list cases =
      INDUCT_TAC(with_fp, `active:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm old_safe = conv_rule(rewrite_conv(THM_LIST(
        cm_region_prefix_safe_def)), assume_rule(
          `cm_region_prefix_safe (p:cm_program)
            (old_regions:(cm_region)list) (fid:int) (fp:int)
            ([]:(cm_region)list) (old:(cm_region)list)`));
    gnode reduced = CONV_TAC(leaf,
        rewrite_conv(THM_LIST(cm_region_prefix_safe_def)));
    ACCEPT_TAC(reduced, old_safe);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list boundary_cases = BOOL_CASES_TAC(
        leaf,
        `(a0:cm_region) :: (a1:(cm_region)list) ==
           (old:(cm_region)list)`,
        "Hboundary");
    {
      CONV_WITH_ASMP_TAC(boundary_cases[0], reduce_rewrite_conv,
          THM_LIST(cm_region_prefix_safe_def));
    }
    {
      thm not_boundary = assume_rule(
          `~((a0:cm_region) :: (a1:(cm_region)list) ==
              (old:(cm_region)list))`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_region_prefix_safe_def, not_boundary)), assume_rule(
            `cm_region_prefix_safe (p:cm_program)
              (old_regions:(cm_region)list) (fid:int) (fp:int)
              ((a0:cm_region) :: (a1:(cm_region)list))
              (old:(cm_region)list)`));
      thm head = match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `p:cm_program`, `new_regions:(cm_region)list`,
            `old_regions:(cm_region)list`, `fid:int`, `fp:int`,
            `a0:cm_region`), cm_region_frame_safe_bases),
          assume_rule(
            `cm_region_bases_equal
              (new_regions:(cm_region)list)
              (old_regions:(cm_region)list)`)),
          conjunct1_rule(opened));
      thm ih = specl_rule(TERM_LIST(
          `old:(cm_region)list`),
          assume_rule(goal_lasmps(boundary_cases[1]->g)[0].tm));
      thm tail = match_mp_rule(match_mp_rule(
          ih, assume_rule(
            `cm_region_bases_equal
              (new_regions:(cm_region)list)
              (old_regions:(cm_region)list)`)),
          conjunct2_rule(opened));
      gnode reduced = CONV_WITH_ASMP_TAC(
          boundary_cases[1], reduce_rewrite_conv,
          THM_LIST(cm_region_prefix_safe_def, not_boundary));
      ACCEPT_TAC(reduced, conj_rule(head, tail));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_region_prefix_safe_bases =
    cm_prove_region_prefix_safe_bases();

PROOF static thm cm_prove_static_regions_layout_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (new_regions:(cm_region)list)
         (old_regions:(cm_region)list).
         cm_region_bases_equal new_regions old_regions ==>
         cm_static_regions_layout p old_regions ==>
         cm_static_regions_layout p new_regions`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_static_regions_layout_def)));
  gnode with_region = GEN_TAC(opened, "region");
  gnode member_leaf = AUTO_INTROS_TAC(with_region);
  thm old_layout = conv_rule(rewrite_conv(THM_LIST(
      cm_static_regions_layout_def)), assume_rule(
        `cm_static_regions_layout (p:cm_program)
          (old_regions:(cm_region)list)`));
  thm old_parts = match_mp_rule(
      spec_rule(`region:cm_region`, old_layout),
      assume_rule(
        `MEM (region:cm_region)
           (cm_static_regions (p:cm_program)) &&
         cm_region_live (region:cm_region)`));
  thm bases = conv_rule(rewrite_conv(THM_LIST(
      cm_region_bases_equal_def)), assume_rule(
        `cm_region_bases_equal
          (new_regions:(cm_region)list)
          (old_regions:(cm_region)list)`));
  thm base_equal = spec_rule(
      `cm_region_gen (region:cm_region)`, bases);
  thm new_parts = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(base_equal))), old_parts);
  ACCEPT_TAC(member_leaf, new_parts);
  return gnode_prove(root);
}
PROOF thm cm_static_regions_layout_bases =
    cm_prove_static_regions_layout_bases();

PROOF static thm cm_prove_runtime_stack_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (new_regions:(cm_region)list)
         (old_regions:(cm_region)list) (cursors:(cm_acursor)list)
         (fid:int) (fp:int) (active:(cm_region)list)
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_region_bases_equal new_regions old_regions ==>
         cm_runtime_stack p old_regions fid fp active cursors
           spills saved calls ==>
         cm_runtime_stack p new_regions fid fp active cursors
           spills saved calls`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_new = GEN_TAC(with_program, "new_regions");
  gnode with_old = GEN_TAC(with_new, "old_regions");
  gnode_list cases =
      INDUCT_TAC(with_old, `cursors:(cm_acursor)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(
        THM_LIST(cm_runtime_stack_def)), assume_rule(
          `cm_runtime_stack (p:cm_program)
            (old_regions:(cm_region)list) (fid:int) (fp:int)
            (active:(cm_region)list) ([]:(cm_acursor)list)
            (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term phase = `cm_cursor_phase (a0:cm_acursor)`;
    thm bases = assume_rule(
        `cm_region_bases_equal
          (new_regions:(cm_region)list)
          (old_regions:(cm_region)list)`);
    thm stack = assume_rule(
        `cm_runtime_stack (p:cm_program)
          (old_regions:(cm_region)list) (fid:int) (fp:int)
          (active:(cm_region)list)
          ((a0:cm_acursor) :: (a1:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`);
    gnode_list call_cases = BOOL_CASES_TAC(
        leaf, `cm_phase_is_call ${phase:cm_aphase}`, "Hcall");
    {
      thm call = assume_rule(
          `cm_phase_is_call ${phase:cm_aphase}`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_runtime_stack_def, call)), stack);
      thm old_prefix = cm_invariant_step_consequence(opened,
          `cm_region_prefix_safe (p:cm_program)
            (old_regions:(cm_region)list) (fid:int) (fp:int)
            (active:(cm_region)list)
            (cm_phase_oldregions ${phase:cm_aphase})`);
      thm new_prefix = match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `p:cm_program`, `new_regions:(cm_region)list`,
            `old_regions:(cm_region)list`, `fid:int`, `fp:int`,
            `active:(cm_region)list`,
            `cm_phase_oldregions ${phase:cm_aphase}`),
            cm_region_prefix_safe_bases),
          bases), old_prefix);
      thm old_recursive = cm_invariant_step_consequence(opened,
          `cm_runtime_stack (p:cm_program)
            (old_regions:(cm_region)list)
            (cm_phase_caller ${phase:cm_aphase})
            (cm_phase_oldfp ${phase:cm_aphase})
            (cm_phase_oldregions ${phase:cm_aphase})
            (a1:(cm_acursor)list)
            (cm_spill_frame_spills
              (HD (saved:(cm_spill_frame)list)))
            (TL saved) (TL (calls:(cm_call_sim_frame)list))`);
      thm ih = specl_rule(TERM_LIST(
          `cm_phase_caller ${phase:cm_aphase}`,
          `cm_phase_oldfp ${phase:cm_aphase}`,
          `cm_phase_oldregions ${phase:cm_aphase}`,
          `cm_spill_frame_spills
            (HD (saved:(cm_spill_frame)list))`,
          `TL (saved:(cm_spill_frame)list)`,
          `TL (calls:(cm_call_sim_frame)list)`),
          assume_rule(goal_lasmps(call_cases[0]->g)[0].tm));
      thm new_recursive = match_mp_rule(match_mp_rule(
          ih, bases), old_recursive);
      gnode reduced = CONV_WITH_ASMP_TAC(
          call_cases[0], reduce_rewrite_conv,
          THM_LIST(cm_runtime_stack_def, call));
      thm facts = conj_rule(opened,
          conj_rule(new_prefix, new_recursive));
      ACCEPT_TAC(reduced, mp_rule(
          taut_rule(mk_imp(concl(facts), goal_ccl(reduced->g))),
          facts));
    }
    {
      thm not_call = assume_rule(
          `~cm_phase_is_call ${phase:cm_aphase}`);
      gnode_list scope_cases = BOOL_CASES_TAC(
          call_cases[1], `cm_phase_is_scope ${phase:cm_aphase}`,
          "Hscope");
      {
        thm scope = assume_rule(
            `cm_phase_is_scope ${phase:cm_aphase}`);
        thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_runtime_stack_def, not_call, scope)), stack);
        thm old_prefix = cm_invariant_step_consequence(opened,
            `cm_region_prefix_safe (p:cm_program)
              (old_regions:(cm_region)list) (fid:int) (fp:int)
              (active:(cm_region)list)
              (cm_phase_oldregions ${phase:cm_aphase})`);
        thm new_prefix = match_mp_rule(match_mp_rule(
            specl_rule(TERM_LIST(
              `p:cm_program`, `new_regions:(cm_region)list`,
              `old_regions:(cm_region)list`, `fid:int`, `fp:int`,
              `active:(cm_region)list`,
              `cm_phase_oldregions ${phase:cm_aphase}`),
              cm_region_prefix_safe_bases),
            bases), old_prefix);
        thm old_recursive = cm_invariant_step_consequence(opened,
            `cm_runtime_stack (p:cm_program)
              (old_regions:(cm_region)list) (fid:int) (fp:int)
              (cm_phase_oldregions ${phase:cm_aphase})
              (a1:(cm_acursor)list) (spills:(cm_spill)list)
              (saved:(cm_spill_frame)list)
              (calls:(cm_call_sim_frame)list)`);
        thm ih = specl_rule(TERM_LIST(
            `fid:int`, `fp:int`,
            `cm_phase_oldregions ${phase:cm_aphase}`,
            `spills:(cm_spill)list`,
            `saved:(cm_spill_frame)list`,
            `calls:(cm_call_sim_frame)list`),
            assume_rule(goal_lasmps(scope_cases[0]->g)[0].tm));
        thm new_recursive = match_mp_rule(match_mp_rule(
            ih, bases), old_recursive);
        gnode reduced = CONV_WITH_ASMP_TAC(
            scope_cases[0], reduce_rewrite_conv,
            THM_LIST(cm_runtime_stack_def, not_call, scope));
        thm facts = conj_rule(opened,
            conj_rule(new_prefix, new_recursive));
        ACCEPT_TAC(reduced, mp_rule(
            taut_rule(mk_imp(concl(facts), goal_ccl(reduced->g))),
            facts));
      }
      {
        thm not_scope = assume_rule(
            `~cm_phase_is_scope ${phase:cm_aphase}`);
        gnode_list halt_cases = BOOL_CASES_TAC(
            scope_cases[1], `cm_phase_is_halt ${phase:cm_aphase}`,
            "Hhalt");
        {
          thm halt = assume_rule(
              `cm_phase_is_halt ${phase:cm_aphase}`);
          thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, halt)), stack);
          thm old_static = cm_invariant_step_consequence(opened,
              `cm_static_regions_layout (p:cm_program)
                (old_regions:(cm_region)list)`);
          thm new_static = match_mp_rule(match_mp_rule(
              specl_rule(TERM_LIST(
                `p:cm_program`, `new_regions:(cm_region)list`,
                `old_regions:(cm_region)list`),
                cm_static_regions_layout_bases),
              bases), old_static);
          gnode reduced = CONV_WITH_ASMP_TAC(
              halt_cases[0], reduce_rewrite_conv,
              THM_LIST(cm_runtime_stack_def, not_call,
                not_scope, halt));
          thm facts = conj_rule(opened, new_static);
          ACCEPT_TAC(reduced, mp_rule(
              taut_rule(mk_imp(concl(facts), goal_ccl(reduced->g))),
              facts));
        }
        {
          thm not_halt = assume_rule(
              `~cm_phase_is_halt ${phase:cm_aphase}`);
          thm old_recursive = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, not_halt)),
              stack);
          thm ih = specl_rule(TERM_LIST(
              `fid:int`, `fp:int`, `active:(cm_region)list`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`),
              assume_rule(goal_lasmps(halt_cases[1]->g)[0].tm));
          thm new_recursive = match_mp_rule(match_mp_rule(
              ih, bases), old_recursive);
          gnode reduced = CONV_WITH_ASMP_TAC(
              halt_cases[1], reduce_rewrite_conv,
              THM_LIST(cm_runtime_stack_def, not_call,
                not_scope, not_halt));
          ACCEPT_TAC(reduced, new_recursive);
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_bases =
    cm_prove_runtime_stack_bases();

PROOF static thm cm_prove_runtime_stack_dead_prefix(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (cursors:(cm_acursor)list) (fid:int) (fp:int)
         (outer:(cm_region)list) (middle:(cm_region)list)
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_region_dead_prefix outer middle ==>
         cm_runtime_stack p all_regions fid fp middle cursors
           spills saved calls ==>
         cm_runtime_stack p all_regions fid fp outer cursors
           spills saved calls`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_all = GEN_TAC(with_program, "all_regions");
  gnode_list cases =
      INDUCT_TAC(with_all, `cursors:(cm_acursor)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(
        THM_LIST(cm_runtime_stack_def)), assume_rule(
          `cm_runtime_stack (p:cm_program)
            (all_regions:(cm_region)list) (fid:int) (fp:int)
            (middle:(cm_region)list) ([]:(cm_acursor)list)
            (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term phase = `cm_cursor_phase (a0:cm_acursor)`;
    thm dead = assume_rule(
        `cm_region_dead_prefix
          (outer:(cm_region)list) (middle:(cm_region)list)`);
    thm stack = assume_rule(
        `cm_runtime_stack (p:cm_program)
          (all_regions:(cm_region)list) (fid:int) (fp:int)
          (middle:(cm_region)list)
          ((a0:cm_acursor) :: (a1:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`);
    gnode_list call_cases = BOOL_CASES_TAC(
        leaf, `cm_phase_is_call ${phase:cm_aphase}`, "Hcall");
    {
      thm call = assume_rule(
          `cm_phase_is_call ${phase:cm_aphase}`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_runtime_stack_def, call)), stack);
      thm middle_prefix = cm_invariant_step_consequence(opened,
          `cm_region_prefix_safe (p:cm_program)
            (all_regions:(cm_region)list) (fid:int) (fp:int)
            (middle:(cm_region)list)
            (cm_phase_oldregions ${phase:cm_aphase})`);
      thm outer_prefix = match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `p:cm_program`, `all_regions:(cm_region)list`,
            `fid:int`, `fp:int`, `outer:(cm_region)list`,
            `middle:(cm_region)list`,
            `cm_phase_oldregions ${phase:cm_aphase}`),
            cm_region_dead_prefix_safe_trans),
          dead), middle_prefix);
      gnode reduced = CONV_WITH_ASMP_TAC(
          call_cases[0], reduce_rewrite_conv,
          THM_LIST(cm_runtime_stack_def, call));
      thm facts = conj_rule(opened, outer_prefix);
      ACCEPT_TAC(reduced, mp_rule(
          taut_rule(mk_imp(concl(facts), goal_ccl(reduced->g))),
          facts));
    }
    {
      thm not_call = assume_rule(
          `~cm_phase_is_call ${phase:cm_aphase}`);
      gnode_list scope_cases = BOOL_CASES_TAC(
          call_cases[1], `cm_phase_is_scope ${phase:cm_aphase}`,
          "Hscope");
      {
        thm scope = assume_rule(
            `cm_phase_is_scope ${phase:cm_aphase}`);
        thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_runtime_stack_def, not_call, scope)), stack);
        thm middle_prefix = cm_invariant_step_consequence(opened,
            `cm_region_prefix_safe (p:cm_program)
              (all_regions:(cm_region)list) (fid:int) (fp:int)
              (middle:(cm_region)list)
              (cm_phase_oldregions ${phase:cm_aphase})`);
        thm outer_prefix = match_mp_rule(match_mp_rule(
            specl_rule(TERM_LIST(
              `p:cm_program`, `all_regions:(cm_region)list`,
              `fid:int`, `fp:int`, `outer:(cm_region)list`,
              `middle:(cm_region)list`,
              `cm_phase_oldregions ${phase:cm_aphase}`),
              cm_region_dead_prefix_safe_trans),
            dead), middle_prefix);
        gnode reduced = CONV_WITH_ASMP_TAC(
            scope_cases[0], reduce_rewrite_conv,
            THM_LIST(cm_runtime_stack_def, not_call, scope));
        thm facts = conj_rule(opened, outer_prefix);
        ACCEPT_TAC(reduced, mp_rule(
            taut_rule(mk_imp(concl(facts), goal_ccl(reduced->g))),
            facts));
      }
      {
        thm not_scope = assume_rule(
            `~cm_phase_is_scope ${phase:cm_aphase}`);
        gnode_list halt_cases = BOOL_CASES_TAC(
            scope_cases[1], `cm_phase_is_halt ${phase:cm_aphase}`,
            "Hhalt");
        {
          thm halt = assume_rule(
              `cm_phase_is_halt ${phase:cm_aphase}`);
          thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, halt)), stack);
          thm middle_static = cm_invariant_step_consequence(opened,
              `cm_region_dead_prefix (middle:(cm_region)list)
                (cm_static_regions (p:cm_program))`);
          thm outer_static = match_mp_rule(match_mp_rule(
              specl_rule(TERM_LIST(
                `outer:(cm_region)list`, `middle:(cm_region)list`,
                `cm_static_regions (p:cm_program)`),
                cm_region_dead_prefix_trans),
              dead), middle_static);
          gnode reduced = CONV_WITH_ASMP_TAC(
              halt_cases[0], reduce_rewrite_conv,
              THM_LIST(cm_runtime_stack_def, not_call,
                not_scope, halt));
          thm facts = conj_rule(opened, outer_static);
          ACCEPT_TAC(reduced, mp_rule(
              taut_rule(mk_imp(concl(facts), goal_ccl(reduced->g))),
              facts));
        }
        {
          thm not_halt = assume_rule(
              `~cm_phase_is_halt ${phase:cm_aphase}`);
          thm recursive = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, not_halt)),
              stack);
          thm ih = specl_rule(TERM_LIST(
              `fid:int`, `fp:int`, `outer:(cm_region)list`,
              `middle:(cm_region)list`, `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`),
              assume_rule(goal_lasmps(halt_cases[1]->g)[0].tm));
          thm result = match_mp_rule(match_mp_rule(
              ih, dead), recursive);
          gnode reduced = CONV_WITH_ASMP_TAC(
              halt_cases[1], reduce_rewrite_conv,
              THM_LIST(cm_runtime_stack_def, not_call,
                not_scope, not_halt));
          ACCEPT_TAC(reduced, result);
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_dead_prefix =
    cm_prove_runtime_stack_dead_prefix();

PROOF static thm cm_prove_runtime_stack_restore(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (restore_fid:int) (restore_fp:int)
         (active:(cm_region)list) (old:(cm_region)list)
         (fid:int) (fp:int) (cursors:(cm_acursor)list)
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_region_prefix_safe p active restore_fid restore_fp
           active old ==>
         cm_runtime_stack p active fid fp old cursors
           spills saved calls ==>
         cm_runtime_stack p (cm_restore_regions active old)
           fid fp (cm_restore_regions active old) cursors
           spills saved calls`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm prefix = assume_rule(
      `cm_region_prefix_safe (p:cm_program)
        (active:(cm_region)list) (restore_fid:int) (restore_fp:int)
        active (old:(cm_region)list)`);
  thm old_stack = assume_rule(
      `cm_runtime_stack (p:cm_program)
        (active:(cm_region)list) (fid:int) (fp:int)
        (old:(cm_region)list) (cursors:(cm_acursor)list)
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`);
  thm bases = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `active:(cm_region)list`,
      `restore_fid:int`, `restore_fp:int`,
      `active:(cm_region)list`, `old:(cm_region)list`),
      cm_restore_regions_bases), prefix);
  thm transferred = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`,
        `cm_restore_regions (active:(cm_region)list)
          (old:(cm_region)list)`,
        `active:(cm_region)list`, `cursors:(cm_acursor)list`,
        `fid:int`, `fp:int`, `old:(cm_region)list`,
        `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
        `calls:(cm_call_sim_frame)list`),
        cm_runtime_stack_bases),
      bases), old_stack);
  thm dead = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `active:(cm_region)list`,
      `restore_fid:int`, `restore_fp:int`,
      `active:(cm_region)list`, `old:(cm_region)list`),
      cm_restore_regions_dead_prefix), prefix);
  thm result = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`,
        `cm_restore_regions (active:(cm_region)list)
          (old:(cm_region)list)`,
        `cursors:(cm_acursor)list`, `fid:int`, `fp:int`,
        `cm_restore_regions (active:(cm_region)list)
          (old:(cm_region)list)`,
        `old:(cm_region)list`, `spills:(cm_spill)list`,
        `saved:(cm_spill_frame)list`,
        `calls:(cm_call_sim_frame)list`),
        cm_runtime_stack_dead_prefix),
      dead), transferred);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_restore =
    cm_prove_runtime_stack_restore();

PROOF static thm cm_prove_regions_before_head(void) {
  gnode root = gnode_new_with_ccl(
      `!(region:cm_region) (rest:(cm_region)list) (limit:int).
         cm_regions_before (region :: rest) limit ==>
         cm_region_gen region < limit`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm before = conv_rule(rewrite_conv(THM_LIST(
      cm_regions_before_def)), assume_rule(
        `cm_regions_before
          ((region:cm_region) :: (rest:(cm_region)list))
          (limit:int)`));
  thm member = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_theorem_by_name("MEM"))),
      `MEM (region:cm_region)
        (region :: (rest:(cm_region)list))`));
  ACCEPT_TAC(leaf, match_mp_rule(
      spec_rule(`region:cm_region`, before), member));
  return gnode_prove(root);
}
PROOF thm cm_regions_before_head =
    cm_prove_regions_before_head();

PROOF static thm cm_prove_regions_before_tail(void) {
  gnode root = gnode_new_with_ccl(
      `!(region:cm_region) (rest:(cm_region)list) (limit:int).
         cm_regions_before (region :: rest) limit ==>
         cm_regions_before rest limit`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm before = conv_rule(rewrite_conv(THM_LIST(
      cm_regions_before_def)), assume_rule(
        `cm_regions_before
          ((region:cm_region) :: (rest:(cm_region)list))
          (limit:int)`));
  gnode reduced = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_regions_before_def)));
  gnode with_candidate = GEN_TAC(reduced, "candidate");
  gnode with_member = DISCH_TAC(with_candidate, "Hmember");
  thm lifted_unfolded = apply_conversion(rewrite_conv(
      THM_LIST(get_theorem_by_name("MEM"))),
      `MEM (candidate:cm_region)
        ((region:cm_region) :: (rest:(cm_region)list))`);
  thm lifted_member = eq_mp_rule(sym_rule(lifted_unfolded),
      disj2_rule(
        `(candidate:cm_region) == (region:cm_region)`,
        assume_rule(
          `MEM (candidate:cm_region) (rest:(cm_region)list)`)));
  ACCEPT_TAC(with_member, match_mp_rule(
      spec_rule(`candidate:cm_region`, before), lifted_member));
  return gnode_prove(root);
}
PROOF thm cm_regions_before_tail =
    cm_prove_regions_before_tail();

PROOF static thm cm_prove_regions_before_cons(void) {
  gnode root = gnode_new_with_ccl(
      `!(region:cm_region) (rest:(cm_region)list) (limit:int).
         cm_region_gen region < limit ==>
         cm_regions_before rest limit ==>
         cm_regions_before (region :: rest) limit`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm tail = conv_rule(rewrite_conv(THM_LIST(
      cm_regions_before_def)), assume_rule(
        `cm_regions_before (rest:(cm_region)list) (limit:int)`));
  gnode reduced = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_regions_before_def)));
  gnode with_candidate = GEN_TAC(reduced, "candidate");
  gnode with_member = DISCH_TAC(with_candidate, "Hmember");
  thm member = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("MEM"))), assume_rule(
        `MEM (candidate:cm_region)
          ((region:cm_region) :: (rest:(cm_region)list))`));
  gnode_list member_cases =
      DISJ_CASES_TAC(with_member, member, "Hmember_part");
  {
    thm equal = assume_rule(
        `(candidate:cm_region) == (region:cm_region)`);
    ACCEPT_TAC(member_cases[0],
        conv_rule(rewrite_conv(THM_LIST(sym_rule(equal))),
          assume_rule(
            `cm_region_gen (region:cm_region) < (limit:int)`)));
  }
  {
    ACCEPT_TAC(member_cases[1], match_mp_rule(
        spec_rule(`candidate:cm_region`, tail),
        assume_rule(
          `MEM (candidate:cm_region) (rest:(cm_region)list)`)));
  }
  return gnode_prove(root);
}
PROOF thm cm_regions_before_cons =
    cm_prove_regions_before_cons();

PROOF static thm cm_prove_restore_regions_before(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (fid:int) (fp:int) (active:(cm_region)list)
         (old:(cm_region)list) (limit:int).
         cm_region_prefix_safe p all_regions fid fp active old ==>
         cm_regions_before active limit ==>
         cm_regions_before (cm_restore_regions active old) limit`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_all = GEN_TAC(with_program, "all_regions");
  gnode with_fid = GEN_TAC(with_all, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode_list cases =
      INDUCT_TAC(with_fp, `active:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm prefix = conv_rule(rewrite_conv(THM_LIST(
        cm_region_prefix_safe_def)), assume_rule(
          `cm_region_prefix_safe (p:cm_program)
            (all_regions:(cm_region)list) (fid:int) (fp:int)
            ([]:(cm_region)list) (old:(cm_region)list)`));
    thm before = assume_rule(
        `cm_regions_before ([]:(cm_region)list) (limit:int)`);
    gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        get_cm_restore_regions_def(), prefix)));
    ACCEPT_TAC(reduced, before);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list boundary_cases = BOOL_CASES_TAC(
        leaf,
        `(a0:cm_region) :: (a1:(cm_region)list) ==
           (old:(cm_region)list)`,
        "Hboundary");
    {
      thm boundary = assume_rule(
          `(a0:cm_region) :: (a1:(cm_region)list) ==
             (old:(cm_region)list)`);
      thm before = assume_rule(
          `cm_regions_before
            ((a0:cm_region) :: (a1:(cm_region)list))
            (limit:int)`);
      gnode reduced = CONV_WITH_ASMP_TAC(
          boundary_cases[0], reduce_rewrite_conv,
          THM_LIST(get_cm_restore_regions_def(), boundary));
      ACCEPT_TAC(reduced,
          conv_rule(rewrite_conv(THM_LIST(boundary)), before));
    }
    {
      thm not_boundary = assume_rule(
          `~((a0:cm_region) :: (a1:(cm_region)list) ==
              (old:(cm_region)list))`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_region_prefix_safe_def, not_boundary)), assume_rule(
            `cm_region_prefix_safe (p:cm_program)
              (all_regions:(cm_region)list) (fid:int) (fp:int)
              ((a0:cm_region) :: (a1:(cm_region)list))
              (old:(cm_region)list)`));
      thm before = assume_rule(
          `cm_regions_before
            ((a0:cm_region) :: (a1:(cm_region)list))
            (limit:int)`);
      thm head_before = match_mp_rule(
          specl_rule(TERM_LIST(
            `a0:cm_region`, `a1:(cm_region)list`, `limit:int`),
            cm_regions_before_head), before);
      thm tail_before = match_mp_rule(
          specl_rule(TERM_LIST(
            `a0:cm_region`, `a1:(cm_region)list`, `limit:int`),
            cm_regions_before_tail), before);
      thm ih = specl_rule(TERM_LIST(
          `old:(cm_region)list`, `limit:int`),
          assume_rule(goal_lasmps(boundary_cases[1]->g)[0].tm));
      thm restored_tail = match_mp_rule(match_mp_rule(
          ih, conjunct2_rule(opened)), tail_before);
      thm retired_gen =
          spec_rule(`a0:cm_region`, cm_retire_region_gen);
      thm retired_bound_eq = beta_norm(ap_term_rule(
          `\x:int. x < (limit:int)`, retired_gen));
      thm retired_before =
          eq_mp_rule(sym_rule(retired_bound_eq), head_before);
      thm result = match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `cm_retire_region (a0:cm_region)`,
            `cm_restore_regions (a1:(cm_region)list)
              (old:(cm_region)list)`,
            `limit:int`), cm_regions_before_cons),
          retired_before), restored_tail);
      gnode reduced = CONV_WITH_ASMP_TAC(
          boundary_cases[1], reduce_rewrite_conv,
          THM_LIST(get_cm_restore_regions_def(), not_boundary));
      ACCEPT_TAC(reduced, result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_restore_regions_before =
    cm_prove_restore_regions_before();

PROOF thm cm_region_bases_below_equal_def = new_fun_definition(
    `cm_region_bases_below_equal
       (left:(cm_region)list) (right:(cm_region)list)
       (limit:int) : bool =
       !gen. gen < limit ==>
         cm_region_base left gen == cm_region_base right gen`);

PROOF static thm cm_prove_regions_before_prefix_suffix(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (fid:int) (fp:int) (active:(cm_region)list)
         (old:(cm_region)list) (limit:int).
         cm_region_prefix_safe p all_regions fid fp active old ==>
         cm_regions_before active limit ==>
         cm_regions_before old limit`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_all = GEN_TAC(with_program, "all_regions");
  gnode with_fid = GEN_TAC(with_all, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode_list cases =
      INDUCT_TAC(with_fp, `active:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm prefix = conv_rule(rewrite_conv(THM_LIST(
        cm_region_prefix_safe_def)), assume_rule(
          `cm_region_prefix_safe (p:cm_program)
            (all_regions:(cm_region)list) (fid:int) (fp:int)
            ([]:(cm_region)list) (old:(cm_region)list)`));
    thm before = assume_rule(
        `cm_regions_before ([]:(cm_region)list) (limit:int)`);
    ACCEPT_TAC(leaf,
        conv_rule(rewrite_conv(THM_LIST(sym_rule(prefix))), before));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list boundary_cases = BOOL_CASES_TAC(
        leaf,
        `(a0:cm_region) :: (a1:(cm_region)list) ==
           (old:(cm_region)list)`,
        "Hboundary");
    {
      thm boundary = assume_rule(
          `(a0:cm_region) :: (a1:(cm_region)list) ==
             (old:(cm_region)list)`);
      ACCEPT_TAC(boundary_cases[0],
          conv_rule(rewrite_conv(THM_LIST(boundary)),
            assume_rule(
              `cm_regions_before
                ((a0:cm_region) :: (a1:(cm_region)list))
                (limit:int)`)));
    }
    {
      thm not_boundary = assume_rule(
          `~((a0:cm_region) :: (a1:(cm_region)list) ==
              (old:(cm_region)list))`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_region_prefix_safe_def, not_boundary)), assume_rule(
            `cm_region_prefix_safe (p:cm_program)
              (all_regions:(cm_region)list) (fid:int) (fp:int)
              ((a0:cm_region) :: (a1:(cm_region)list))
              (old:(cm_region)list)`));
      thm tail_before = match_mp_rule(
          specl_rule(TERM_LIST(
            `a0:cm_region`, `a1:(cm_region)list`, `limit:int`),
            cm_regions_before_tail), assume_rule(
              `cm_regions_before
                ((a0:cm_region) :: (a1:(cm_region)list))
                (limit:int)`));
      thm ih = specl_rule(TERM_LIST(
          `old:(cm_region)list`, `limit:int`),
          assume_rule(goal_lasmps(boundary_cases[1]->g)[0].tm));
      ACCEPT_TAC(boundary_cases[1],
          match_mp_rule(match_mp_rule(
            ih, conjunct2_rule(opened)), tail_before));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_regions_before_prefix_suffix =
    cm_prove_regions_before_prefix_suffix();

PROOF static thm cm_prove_regions_before_dead_suffix(void) {
  gnode root = gnode_new_with_ccl(
      `!(active:(cm_region)list) (old:(cm_region)list)
         (limit:int).
         cm_region_dead_prefix active old ==>
         cm_regions_before active limit ==>
         cm_regions_before old limit`);
  gnode_list cases =
      INDUCT_TAC(root, `active:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm prefix = conv_rule(rewrite_conv(THM_LIST(
        cm_region_dead_prefix_def)), assume_rule(
          `cm_region_dead_prefix
            ([]:(cm_region)list) (old:(cm_region)list)`));
    thm before = assume_rule(
        `cm_regions_before ([]:(cm_region)list) (limit:int)`);
    ACCEPT_TAC(leaf,
        conv_rule(rewrite_conv(THM_LIST(sym_rule(prefix))), before));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list boundary_cases = BOOL_CASES_TAC(
        leaf,
        `(a0:cm_region) :: (a1:(cm_region)list) ==
           (old:(cm_region)list)`,
        "Hboundary");
    {
      thm boundary = assume_rule(
          `(a0:cm_region) :: (a1:(cm_region)list) ==
             (old:(cm_region)list)`);
      ACCEPT_TAC(boundary_cases[0],
          conv_rule(rewrite_conv(THM_LIST(boundary)),
            assume_rule(
              `cm_regions_before
                ((a0:cm_region) :: (a1:(cm_region)list))
                (limit:int)`)));
    }
    {
      thm not_boundary = assume_rule(
          `~((a0:cm_region) :: (a1:(cm_region)list) ==
              (old:(cm_region)list))`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_region_dead_prefix_def, not_boundary)), assume_rule(
            `cm_region_dead_prefix
              ((a0:cm_region) :: (a1:(cm_region)list))
              (old:(cm_region)list)`));
      thm tail_before = match_mp_rule(
          specl_rule(TERM_LIST(
            `a0:cm_region`, `a1:(cm_region)list`, `limit:int`),
            cm_regions_before_tail), assume_rule(
              `cm_regions_before
                ((a0:cm_region) :: (a1:(cm_region)list))
                (limit:int)`));
      thm ih = specl_rule(TERM_LIST(
          `old:(cm_region)list`, `limit:int`),
          assume_rule(goal_lasmps(boundary_cases[1]->g)[0].tm));
      ACCEPT_TAC(boundary_cases[1],
          match_mp_rule(match_mp_rule(
            ih, conjunct2_rule(opened)), tail_before));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_regions_before_dead_suffix =
    cm_prove_regions_before_dead_suffix();

PROOF static thm cm_prove_region_frame_safe_below_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (new_regions:(cm_region)list)
         (old_regions:(cm_region)list) (limit:int)
         (fid:int) (fp:int) (region:cm_region).
         cm_region_bases_below_equal new_regions old_regions limit ==>
         cm_region_gen region < limit ==>
         cm_region_frame_safe p old_regions fid fp region ==>
         cm_region_frame_safe p new_regions fid fp region`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm bases = conv_rule(rewrite_conv(THM_LIST(
      cm_region_bases_below_equal_def)), assume_rule(
        `cm_region_bases_below_equal
          (new_regions:(cm_region)list)
          (old_regions:(cm_region)list) (limit:int)`));
  thm base = match_mp_rule(
      spec_rule(`cm_region_gen (region:cm_region)`, bases),
      assume_rule(
        `cm_region_gen (region:cm_region) < (limit:int)`));
  thm old_safe = conv_rule(rewrite_conv(THM_LIST(
      cm_region_frame_safe_def)), assume_rule(
        `cm_region_frame_safe (p:cm_program)
          (old_regions:(cm_region)list) (fid:int) (fp:int)
          (region:cm_region)`));
  thm transported = conv_rule(pure_rewrite_conv(
      THM_LIST(sym_rule(base))), old_safe);
  gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_region_frame_safe_def)));
  ACCEPT_TAC(reduced, transported);
  return gnode_prove(root);
}
PROOF thm cm_region_frame_safe_below_bases =
    cm_prove_region_frame_safe_below_bases();

PROOF static thm cm_prove_region_prefix_safe_below_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (new_regions:(cm_region)list)
         (old_regions:(cm_region)list) (limit:int)
         (fid:int) (fp:int) (active:(cm_region)list)
         (old:(cm_region)list).
         cm_region_bases_below_equal new_regions old_regions limit ==>
         cm_regions_before active limit ==>
         cm_region_prefix_safe p old_regions fid fp active old ==>
         cm_region_prefix_safe p new_regions fid fp active old`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_new = GEN_TAC(with_program, "new_regions");
  gnode with_old_regions = GEN_TAC(with_new, "old_regions");
  gnode with_limit = GEN_TAC(with_old_regions, "limit");
  gnode with_fid = GEN_TAC(with_limit, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode_list cases =
      INDUCT_TAC(with_fp, `active:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm old_prefix = conv_rule(rewrite_conv(THM_LIST(
        cm_region_prefix_safe_def)), assume_rule(
          `cm_region_prefix_safe (p:cm_program)
            (old_regions:(cm_region)list) (fid:int) (fp:int)
            ([]:(cm_region)list) (old:(cm_region)list)`));
    gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        cm_region_prefix_safe_def)));
    ACCEPT_TAC(reduced, old_prefix);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list boundary_cases = BOOL_CASES_TAC(
        leaf,
        `(a0:cm_region) :: (a1:(cm_region)list) ==
           (old:(cm_region)list)`,
        "Hboundary");
    {
      CONV_WITH_ASMP_TAC(boundary_cases[0],
          reduce_rewrite_conv,
          THM_LIST(cm_region_prefix_safe_def));
    }
    {
      thm not_boundary = assume_rule(
          `~((a0:cm_region) :: (a1:(cm_region)list) ==
              (old:(cm_region)list))`);
      thm old_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_region_prefix_safe_def, not_boundary)), assume_rule(
            `cm_region_prefix_safe (p:cm_program)
              (old_regions:(cm_region)list) (fid:int) (fp:int)
              ((a0:cm_region) :: (a1:(cm_region)list))
              (old:(cm_region)list)`));
      thm before = assume_rule(
          `cm_regions_before
            ((a0:cm_region) :: (a1:(cm_region)list))
            (limit:int)`);
      thm head_before = match_mp_rule(
          specl_rule(TERM_LIST(
            `a0:cm_region`, `a1:(cm_region)list`, `limit:int`),
            cm_regions_before_head), before);
      thm tail_before = match_mp_rule(
          specl_rule(TERM_LIST(
            `a0:cm_region`, `a1:(cm_region)list`, `limit:int`),
            cm_regions_before_tail), before);
      thm bases = assume_rule(
          `cm_region_bases_below_equal
            (new_regions:(cm_region)list)
            (old_regions:(cm_region)list) (limit:int)`);
      thm head_safe = match_mp_rule(match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `p:cm_program`, `new_regions:(cm_region)list`,
            `old_regions:(cm_region)list`, `limit:int`,
            `fid:int`, `fp:int`, `a0:cm_region`),
            cm_region_frame_safe_below_bases),
          bases), head_before), conjunct1_rule(old_opened));
      thm ih = specl_rule(TERM_LIST(
          `old:(cm_region)list`),
          assume_rule(goal_lasmps(boundary_cases[1]->g)[0].tm));
      thm tail_safe = match_mp_rule(match_mp_rule(match_mp_rule(
          ih, bases), tail_before), conjunct2_rule(old_opened));
      thm result = conj_rule(head_safe, tail_safe);
      gnode reduced = CONV_WITH_ASMP_TAC(
          boundary_cases[1], reduce_rewrite_conv,
          THM_LIST(cm_region_prefix_safe_def, not_boundary));
      ACCEPT_TAC(reduced, result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_region_prefix_safe_below_bases =
    cm_prove_region_prefix_safe_below_bases();

PROOF static thm cm_prove_static_regions_layout_below_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (new_regions:(cm_region)list)
         (old_regions:(cm_region)list) (limit:int).
         cm_region_bases_below_equal new_regions old_regions limit ==>
         cm_regions_before (cm_static_regions p) limit ==>
         cm_static_regions_layout p old_regions ==>
         cm_static_regions_layout p new_regions`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm bases = conv_rule(rewrite_conv(THM_LIST(
      cm_region_bases_below_equal_def)), assume_rule(
        `cm_region_bases_below_equal
          (new_regions:(cm_region)list)
          (old_regions:(cm_region)list) (limit:int)`));
  thm before = conv_rule(rewrite_conv(THM_LIST(
      cm_regions_before_def)), assume_rule(
        `cm_regions_before
          (cm_static_regions (p:cm_program)) (limit:int)`));
  thm old_layout = conv_rule(rewrite_conv(THM_LIST(
      cm_static_regions_layout_def)), assume_rule(
        `cm_static_regions_layout (p:cm_program)
          (old_regions:(cm_region)list)`));
  gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_static_regions_layout_def)));
  gnode with_region = GEN_TAC(reduced, "region");
  gnode with_premise = DISCH_TAC(with_region, "Hregion");
  thm premise = assume_rule(
      `MEM (region:cm_region)
         (cm_static_regions (p:cm_program)) &&
       cm_region_live region`);
  thm bound = match_mp_rule(
      spec_rule(`region:cm_region`, before),
      conjunct1_rule(premise));
  thm base = match_mp_rule(
      spec_rule(`cm_region_gen (region:cm_region)`, bases),
      bound);
  thm old_result = match_mp_rule(
      spec_rule(`region:cm_region`, old_layout), premise);
  ACCEPT_TAC(with_premise, conv_rule(pure_rewrite_conv(
      THM_LIST(sym_rule(base))), old_result));
  return gnode_prove(root);
}
PROOF thm cm_static_regions_layout_below_bases =
    cm_prove_static_regions_layout_below_bases();

PROOF static thm cm_prove_runtime_stack_below_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (new_regions:(cm_region)list)
         (old_regions:(cm_region)list) (limit:int)
         (cursors:(cm_acursor)list)
         (fid:int) (fp:int) (active:(cm_region)list)
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_region_bases_below_equal
           new_regions old_regions limit ==>
         cm_regions_before active limit ==>
         cm_runtime_stack p old_regions fid fp active cursors
           spills saved calls ==>
         cm_runtime_stack p new_regions fid fp active cursors
           spills saved calls`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_new = GEN_TAC(with_program, "new_regions");
  gnode with_old = GEN_TAC(with_new, "old_regions");
  gnode with_limit = GEN_TAC(with_old, "limit");
  gnode_list cases =
      INDUCT_TAC(with_limit, `cursors:(cm_acursor)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(
        THM_LIST(cm_runtime_stack_def)), assume_rule(
          `cm_runtime_stack (p:cm_program)
            (old_regions:(cm_region)list) (fid:int) (fp:int)
            (active:(cm_region)list) ([]:(cm_acursor)list)
            (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term phase = `cm_cursor_phase (a0:cm_acursor)`;
    thm bases = assume_rule(
        `cm_region_bases_below_equal
          (new_regions:(cm_region)list)
          (old_regions:(cm_region)list) (limit:int)`);
    thm before = assume_rule(
        `cm_regions_before
          (active:(cm_region)list) (limit:int)`);
    thm stack = assume_rule(
        `cm_runtime_stack (p:cm_program)
          (old_regions:(cm_region)list) (fid:int) (fp:int)
          (active:(cm_region)list)
          ((a0:cm_acursor) :: (a1:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`);
    gnode_list call_cases = BOOL_CASES_TAC(
        leaf, `cm_phase_is_call ${phase:cm_aphase}`, "Hcall");
    {
      thm call = assume_rule(
          `cm_phase_is_call ${phase:cm_aphase}`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_runtime_stack_def, call)), stack);
      thm old_prefix = cm_invariant_step_consequence(opened,
          `cm_region_prefix_safe (p:cm_program)
            (old_regions:(cm_region)list) (fid:int) (fp:int)
            (active:(cm_region)list)
            (cm_phase_oldregions ${phase:cm_aphase})`);
      thm new_prefix = match_mp_rule(match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `p:cm_program`, `new_regions:(cm_region)list`,
            `old_regions:(cm_region)list`, `limit:int`,
            `fid:int`, `fp:int`, `active:(cm_region)list`,
            `cm_phase_oldregions ${phase:cm_aphase}`),
            cm_region_prefix_safe_below_bases),
          bases), before), old_prefix);
      thm old_before = match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `p:cm_program`, `old_regions:(cm_region)list`,
            `fid:int`, `fp:int`, `active:(cm_region)list`,
            `cm_phase_oldregions ${phase:cm_aphase}`,
            `limit:int`), cm_regions_before_prefix_suffix),
          old_prefix), before);
      thm old_recursive = cm_invariant_step_consequence(opened,
          `cm_runtime_stack (p:cm_program)
            (old_regions:(cm_region)list)
            (cm_phase_caller ${phase:cm_aphase})
            (cm_phase_oldfp ${phase:cm_aphase})
            (cm_phase_oldregions ${phase:cm_aphase})
            (a1:(cm_acursor)list)
            (cm_spill_frame_spills
              (HD (saved:(cm_spill_frame)list)))
            (TL saved) (TL (calls:(cm_call_sim_frame)list))`);
      thm ih = specl_rule(TERM_LIST(
          `cm_phase_caller ${phase:cm_aphase}`,
          `cm_phase_oldfp ${phase:cm_aphase}`,
          `cm_phase_oldregions ${phase:cm_aphase}`,
          `cm_spill_frame_spills
            (HD (saved:(cm_spill_frame)list))`,
          `TL (saved:(cm_spill_frame)list)`,
          `TL (calls:(cm_call_sim_frame)list)`),
          assume_rule(goal_lasmps(call_cases[0]->g)[0].tm));
      thm new_recursive = match_mp_rule(match_mp_rule(
          match_mp_rule(ih, bases), old_before), old_recursive);
      gnode reduced = CONV_WITH_ASMP_TAC(
          call_cases[0], reduce_rewrite_conv,
          THM_LIST(cm_runtime_stack_def, call));
      thm facts = conj_rule(opened,
          conj_rule(new_prefix, new_recursive));
      ACCEPT_TAC(reduced, mp_rule(
          taut_rule(mk_imp(concl(facts), goal_ccl(reduced->g))),
          facts));
    }
    {
      thm not_call = assume_rule(
          `~cm_phase_is_call ${phase:cm_aphase}`);
      gnode_list scope_cases = BOOL_CASES_TAC(
          call_cases[1], `cm_phase_is_scope ${phase:cm_aphase}`,
          "Hscope");
      {
        thm scope = assume_rule(
            `cm_phase_is_scope ${phase:cm_aphase}`);
        thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_runtime_stack_def, not_call, scope)), stack);
        thm old_prefix = cm_invariant_step_consequence(opened,
            `cm_region_prefix_safe (p:cm_program)
              (old_regions:(cm_region)list) (fid:int) (fp:int)
              (active:(cm_region)list)
              (cm_phase_oldregions ${phase:cm_aphase})`);
        thm new_prefix = match_mp_rule(match_mp_rule(match_mp_rule(
            specl_rule(TERM_LIST(
              `p:cm_program`, `new_regions:(cm_region)list`,
              `old_regions:(cm_region)list`, `limit:int`,
              `fid:int`, `fp:int`, `active:(cm_region)list`,
              `cm_phase_oldregions ${phase:cm_aphase}`),
              cm_region_prefix_safe_below_bases),
            bases), before), old_prefix);
        thm old_before = match_mp_rule(match_mp_rule(
            specl_rule(TERM_LIST(
              `p:cm_program`, `old_regions:(cm_region)list`,
              `fid:int`, `fp:int`, `active:(cm_region)list`,
              `cm_phase_oldregions ${phase:cm_aphase}`,
              `limit:int`), cm_regions_before_prefix_suffix),
            old_prefix), before);
        thm old_recursive = cm_invariant_step_consequence(opened,
            `cm_runtime_stack (p:cm_program)
              (old_regions:(cm_region)list) (fid:int) (fp:int)
              (cm_phase_oldregions ${phase:cm_aphase})
              (a1:(cm_acursor)list) (spills:(cm_spill)list)
              (saved:(cm_spill_frame)list)
              (calls:(cm_call_sim_frame)list)`);
        thm ih = specl_rule(TERM_LIST(
            `fid:int`, `fp:int`,
            `cm_phase_oldregions ${phase:cm_aphase}`,
            `spills:(cm_spill)list`,
            `saved:(cm_spill_frame)list`,
            `calls:(cm_call_sim_frame)list`),
            assume_rule(goal_lasmps(scope_cases[0]->g)[0].tm));
        thm new_recursive = match_mp_rule(match_mp_rule(
            match_mp_rule(ih, bases), old_before), old_recursive);
        gnode reduced = CONV_WITH_ASMP_TAC(
            scope_cases[0], reduce_rewrite_conv,
            THM_LIST(cm_runtime_stack_def, not_call, scope));
        thm facts = conj_rule(opened,
            conj_rule(new_prefix, new_recursive));
        ACCEPT_TAC(reduced, mp_rule(
            taut_rule(mk_imp(concl(facts), goal_ccl(reduced->g))),
            facts));
      }
      {
        thm not_scope = assume_rule(
            `~cm_phase_is_scope ${phase:cm_aphase}`);
        gnode_list halt_cases = BOOL_CASES_TAC(
            scope_cases[1], `cm_phase_is_halt ${phase:cm_aphase}`,
            "Hhalt");
        {
          thm halt = assume_rule(
              `cm_phase_is_halt ${phase:cm_aphase}`);
          thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, halt)),
              stack);
          thm dead = cm_invariant_step_consequence(opened,
              `cm_region_dead_prefix
                (active:(cm_region)list)
                (cm_static_regions (p:cm_program))`);
          thm static_before = match_mp_rule(match_mp_rule(
              specl_rule(TERM_LIST(
                `active:(cm_region)list`,
                `cm_static_regions (p:cm_program)`, `limit:int`),
                cm_regions_before_dead_suffix),
              dead), before);
          thm old_static = cm_invariant_step_consequence(opened,
              `cm_static_regions_layout (p:cm_program)
                (old_regions:(cm_region)list)`);
          thm new_static = match_mp_rule(match_mp_rule(match_mp_rule(
              specl_rule(TERM_LIST(
                `p:cm_program`, `new_regions:(cm_region)list`,
                `old_regions:(cm_region)list`, `limit:int`),
                cm_static_regions_layout_below_bases),
              bases), static_before), old_static);
          gnode reduced = CONV_WITH_ASMP_TAC(
              halt_cases[0], reduce_rewrite_conv,
              THM_LIST(cm_runtime_stack_def, not_call,
                not_scope, halt));
          thm facts = conj_rule(opened, new_static);
          ACCEPT_TAC(reduced, mp_rule(
              taut_rule(mk_imp(concl(facts), goal_ccl(reduced->g))),
              facts));
        }
        {
          thm not_halt = assume_rule(
              `~cm_phase_is_halt ${phase:cm_aphase}`);
          thm old_recursive = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, not_halt)),
              stack);
          thm ih = specl_rule(TERM_LIST(
              `fid:int`, `fp:int`, `active:(cm_region)list`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`),
              assume_rule(goal_lasmps(halt_cases[1]->g)[0].tm));
          thm new_recursive = match_mp_rule(match_mp_rule(
              match_mp_rule(ih, bases), before), old_recursive);
          gnode reduced = CONV_WITH_ASMP_TAC(
              halt_cases[1], reduce_rewrite_conv,
              THM_LIST(cm_runtime_stack_def, not_call,
                not_scope, not_halt));
          ACCEPT_TAC(reduced, new_recursive);
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_below_bases =
    cm_prove_runtime_stack_below_bases();

PROOF static thm cm_prove_region_bases_below_equal_refl(void) {
  gnode root = gnode_new_with_ccl(
      `!(regions:(cm_region)list) (limit:int).
         cm_region_bases_below_equal regions regions limit`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_region_bases_below_equal_def)));
  return gnode_prove(root);
}
PROOF thm cm_region_bases_below_equal_refl =
    cm_prove_region_bases_below_equal_refl();

PROOF static thm cm_prove_region_bases_below_equal_trans(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:(cm_region)list) (middle:(cm_region)list)
         (right:(cm_region)list) (limit:int).
         cm_region_bases_below_equal left middle limit ==>
         cm_region_bases_below_equal middle right limit ==>
         cm_region_bases_below_equal left right limit`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm left_middle = conv_rule(rewrite_conv(THM_LIST(
      cm_region_bases_below_equal_def)), assume_rule(
        `cm_region_bases_below_equal
          (left:(cm_region)list) (middle:(cm_region)list)
          (limit:int)`));
  thm middle_right = conv_rule(rewrite_conv(THM_LIST(
      cm_region_bases_below_equal_def)), assume_rule(
        `cm_region_bases_below_equal
          (middle:(cm_region)list) (right:(cm_region)list)
          (limit:int)`));
  gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_region_bases_below_equal_def)));
  gnode with_gen = GEN_TAC(reduced, "gen");
  gnode with_bound = DISCH_TAC(with_gen, "Hbound");
  thm bound = assume_rule(`(gen:int) < (limit:int)`);
  ACCEPT_TAC(with_bound, trans_rule(
      match_mp_rule(spec_rule(`gen:int`, left_middle), bound),
      match_mp_rule(spec_rule(`gen:int`, middle_right), bound)));
  return gnode_prove(root);
}
PROOF thm cm_region_bases_below_equal_trans =
    cm_prove_region_bases_below_equal_trans();

PROOF static thm cm_prove_region_bases_fresh_cons(void) {
  gnode root = gnode_new_with_ccl(
      `!(region:cm_region) (regions:(cm_region)list)
         (limit:int).
         limit <= cm_region_gen region ==>
         cm_region_bases_below_equal
           (region :: regions) regions limit`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_region_bases_below_equal_def)));
  gnode with_gen = GEN_TAC(reduced, "gen");
  gnode with_bound = DISCH_TAC(with_gen, "Hbound");
  thm distinct = mp_rule(mp_rule(
      int_arith_rule(
        `(gen:int) < (limit:int) ==>
         limit <= cm_region_gen (region:cm_region) ==>
         ~(gen == cm_region_gen region)`),
      assume_rule(`(gen:int) < (limit:int)`)),
      assume_rule(
        `(limit:int) <= cm_region_gen (region:cm_region)`));
  CONV_WITH_ASMP_TAC(with_bound, reduce_rewrite_conv,
      THM_LIST(get_cm_region_base_def(), distinct));
  return gnode_prove(root);
}
PROOF thm cm_region_bases_fresh_cons =
    cm_prove_region_bases_fresh_cons();

PROOF static thm cm_prove_region_gen_lower_tail(void) {
  gnode root = gnode_new_with_ccl(
      `!(head:cm_region) (tail:(cm_region)list) (limit:int).
         (!region. MEM region (head :: tail) ==>
            limit <= cm_region_gen region) ==>
         !region. MEM region tail ==>
            limit <= cm_region_gen region`);
  gnode with_head = GEN_TAC(root, "head");
  gnode with_tail = GEN_TAC(with_head, "tail");
  gnode with_limit = GEN_TAC(with_tail, "limit");
  gnode with_lower = DISCH_TAC(with_limit, "Hlower");
  gnode with_region = GEN_TAC(with_lower, "region");
  gnode leaf = DISCH_TAC(with_region, "Hmember");
  thm unfolded = apply_conversion(
      rewrite_conv(THM_LIST(get_theorem_by_name("MEM"))),
      `MEM (region:cm_region)
        ((head:cm_region) :: (tail:(cm_region)list))`);
  thm member = eq_mp_rule(sym_rule(unfolded),
      disj2_rule(
        `(region:cm_region) == (head:cm_region)`,
        assume_rule(
          `MEM (region:cm_region) (tail:(cm_region)list)`)));
  ACCEPT_TAC(leaf, match_mp_rule(
      spec_rule(`region:cm_region`, assume_rule(
        `!candidate:cm_region.
           MEM candidate
             ((head:cm_region) :: (tail:(cm_region)list)) ==>
           (limit:int) <= cm_region_gen candidate`)),
      member));
  return gnode_prove(root);
}
PROOF thm cm_region_gen_lower_tail =
    cm_prove_region_gen_lower_tail();

PROOF static thm cm_prove_region_bases_fresh_append(void) {
  gnode root = gnode_new_with_ccl(
      `!(fresh:(cm_region)list) (regions:(cm_region)list)
         (limit:int).
         (!region. MEM region fresh ==>
            limit <= cm_region_gen region) ==>
         cm_region_bases_below_equal
           (fresh ++ regions) regions limit`);
  gnode_list cases =
      INDUCT_TAC(root, `fresh:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND"),
        cm_region_bases_below_equal_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm lower = assume_rule(
        `!region:cm_region.
           MEM region ((a0:cm_region) :: (a1:(cm_region)list)) ==>
           (limit:int) <= cm_region_gen region`);
    thm head_member = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(get_theorem_by_name("MEM"))),
        `MEM (a0:cm_region)
          ((a0:cm_region) :: (a1:(cm_region)list))`));
    thm head_lower = match_mp_rule(
        spec_rule(`a0:cm_region`, lower), head_member);
    thm tail_lower = match_mp_rule(
        specl_rule(TERM_LIST(
          `a0:cm_region`, `a1:(cm_region)list`, `limit:int`),
          cm_region_gen_lower_tail),
        lower);
    thm ih = specl_rule(TERM_LIST(
        `regions:(cm_region)list`, `limit:int`),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    thm tail_bases = match_mp_rule(ih, tail_lower);
    thm head_bases = match_mp_rule(
        specl_rule(TERM_LIST(
          `a0:cm_region`,
          `(a1:(cm_region)list) ++ (regions:(cm_region)list)`,
          `limit:int`), cm_region_bases_fresh_cons),
        head_lower);
    thm result = match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `(a0:cm_region) ::
             ((a1:(cm_region)list) ++ (regions:(cm_region)list))`,
          `(a1:(cm_region)list) ++ (regions:(cm_region)list)`,
          `regions:(cm_region)list`, `limit:int`),
          cm_region_bases_below_equal_trans),
        head_bases), tail_bases);
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND"))));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_region_bases_fresh_append =
    cm_prove_region_bases_fresh_append();

PROOF static thm cm_prove_regions_before_append(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:(cm_region)list) (right:(cm_region)list)
         (limit:int).
         cm_regions_before left limit ==>
         cm_regions_before right limit ==>
         cm_regions_before (left ++ right) limit`);
  gnode_list cases =
      INDUCT_TAC(root, `left:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND"))));
    ACCEPT_TAC(reduced, assume_rule(
        `cm_regions_before
          (right:(cm_region)list) (limit:int)`));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm before = assume_rule(
        `cm_regions_before
          ((a0:cm_region) :: (a1:(cm_region)list))
          (limit:int)`);
    thm head_before = match_mp_rule(
        specl_rule(TERM_LIST(
          `a0:cm_region`, `a1:(cm_region)list`, `limit:int`),
          cm_regions_before_head), before);
    thm tail_before = match_mp_rule(
        specl_rule(TERM_LIST(
          `a0:cm_region`, `a1:(cm_region)list`, `limit:int`),
          cm_regions_before_tail), before);
    thm ih = specl_rule(TERM_LIST(
        `right:(cm_region)list`, `limit:int`),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    thm tail_result = match_mp_rule(match_mp_rule(
        ih, tail_before), assume_rule(
          `cm_regions_before
            (right:(cm_region)list) (limit:int)`));
    thm result = match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `a0:cm_region`,
          `(a1:(cm_region)list) ++ (right:(cm_region)list)`,
          `limit:int`), cm_regions_before_cons),
        head_before), tail_result);
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND"))));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_regions_before_append =
    cm_prove_regions_before_append();

PROOF static thm cm_prove_regions_for_slots_gen_lower(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list)
         (gen:int) (base:int) (region:cm_region).
         MEM region (cm_regions_for_slots structs slots gen base) ==>
         gen <= cm_region_gen region`);
  gnode with_structs = GEN_TAC(root, "structs");
  thm_list region_rules = THM_LIST(
      get_cm_regions_for_slots_def(),
      get_theorem_by_name("MEM"));
  gnode_list cases =
      INDUCT_TAC(with_structs, `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(region_rules),
        assume_rule(
          `MEM (region:cm_region)
            (cm_regions_for_slots
              (structs:(cm_struct_d)list)
              ([]:(cm_slot_d)list) (gen:int) (base:int))`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term head = `CMRegion (gen:int) (base:int) 0i
        (cm_slot_size (structs:(cm_struct_d)list)
          (a0:cm_slot_d)) T T`;
    term tail = `cm_regions_for_slots
        (structs:(cm_struct_d)list) (a1:(cm_slot_d)list)
        ((gen:int) + 1i)
        ((base:int) +
          cm_slot_size structs (a0:cm_slot_d))`;
    thm member = conv_rule(reduce_rewrite_conv(region_rules),
        assume_rule(
          `MEM (region:cm_region)
            (cm_regions_for_slots
              (structs:(cm_struct_d)list)
              ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))
              (gen:int) (base:int))`));
    dest_disj_results member_parts = dest_disj(concl(member));
    thm equal = assume_rule(member_parts.tm1);
    thm head_gen = conv_rule(reduce_rewrite_conv(
        get_cm_runtime_defs()),
        ap_term_rule(`cm_region_gen`, equal));
    thm head_result = mp_rule(
        int_arith_rule(
          `cm_region_gen (region:cm_region) == (gen:int) ==>
           gen <= cm_region_gen region`),
        head_gen);
    thm ih = specl_rule(TERM_LIST(
        `(gen:int) + 1i`,
        `(base:int) +
          cm_slot_size (structs:(cm_struct_d)list)
            (a0:cm_slot_d)`,
        `region:cm_region`),
        cm_invariant_step_assumption(leaf,
          `!(next_gen:int) (next_base:int)
             (candidate:cm_region).
             MEM candidate
               (cm_regions_for_slots
                 (structs:(cm_struct_d)list)
                 (a1:(cm_slot_d)list)
                 next_gen next_base) ==>
             next_gen <= cm_region_gen candidate`));
    thm tail_lower =
        match_mp_rule(ih, assume_rule(member_parts.tm2));
    thm tail_result = mp_rule(
        int_arith_rule(
          `(gen:int) + 1i <= cm_region_gen (region:cm_region) ==>
           gen <= cm_region_gen region`),
        tail_lower);
    ACCEPT_TAC(leaf,
        disj_cases_rule(member, head_result, tail_result));
  }
  return gnode_prove(root);
}
PROOF thm cm_regions_for_slots_gen_lower =
    cm_prove_regions_for_slots_gen_lower();

PROOF static thm cm_prove_regions_for_slots_gen_upper(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list)
         (gen:int) (base:int) (region:cm_region).
         MEM region (cm_regions_for_slots structs slots gen base) ==>
         cm_region_gen region < gen + ilength slots`);
  gnode with_structs = GEN_TAC(root, "structs");
  thm_list region_rules = THM_LIST(
      get_cm_regions_for_slots_def(),
      get_theorem_by_name("MEM"));
  gnode_list cases =
      INDUCT_TAC(with_structs, `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(region_rules),
        assume_rule(
          `MEM (region:cm_region)
            (cm_regions_for_slots
              (structs:(cm_struct_d)list)
              ([]:(cm_slot_d)list) (gen:int) (base:int))`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term head = `CMRegion (gen:int) (base:int) 0i
        (cm_slot_size (structs:(cm_struct_d)list)
          (a0:cm_slot_d)) T T`;
    term tail = `cm_regions_for_slots
        (structs:(cm_struct_d)list) (a1:(cm_slot_d)list)
        ((gen:int) + 1i)
        ((base:int) +
          cm_slot_size structs (a0:cm_slot_d))`;
    thm member = conv_rule(reduce_rewrite_conv(region_rules),
        assume_rule(
          `MEM (region:cm_region)
            (cm_regions_for_slots
              (structs:(cm_struct_d)list)
              ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))
              (gen:int) (base:int))`));
    dest_disj_results member_parts = dest_disj(concl(member));
    thm slots_length = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        `ilength
          ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`);
    thm equal = assume_rule(member_parts.tm1);
    thm head_gen = conv_rule(reduce_rewrite_conv(
        get_cm_runtime_defs()),
        ap_term_rule(`cm_region_gen`, equal));
    thm tail_nonnegative = ispec_rule(
        `a1:(cm_slot_d)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm head_result = mp_rule(mp_rule(
        int_arith_rule(
          `cm_region_gen (region:cm_region) == (gen:int) ==>
           ilength
             ((a0:cm_slot_d) :: (a1:(cm_slot_d)list)) ==
               1i + ilength a1 ==>
           0i <= ilength a1 ==>
           cm_region_gen region <
             gen + ilength (a0 :: a1)`),
        head_gen), slots_length);
    head_result = mp_rule(head_result, tail_nonnegative);
    thm ih = specl_rule(TERM_LIST(
        `(gen:int) + 1i`,
        `(base:int) +
          cm_slot_size (structs:(cm_struct_d)list)
            (a0:cm_slot_d)`,
        `region:cm_region`),
        cm_invariant_step_assumption(leaf,
          `!(next_gen:int) (next_base:int)
             (candidate:cm_region).
             MEM candidate
               (cm_regions_for_slots
                 (structs:(cm_struct_d)list)
                 (a1:(cm_slot_d)list)
                 next_gen next_base) ==>
             cm_region_gen candidate <
               next_gen + ilength (a1:(cm_slot_d)list)`));
    thm tail_upper =
        match_mp_rule(ih, assume_rule(member_parts.tm2));
    thm tail_result = mp_rule(mp_rule(
        int_arith_rule(
          `cm_region_gen (region:cm_region) <
             ((gen:int) + 1i) +
               ilength (a1:(cm_slot_d)list) ==>
           ilength
             ((a0:cm_slot_d) :: (a1:(cm_slot_d)list)) ==
               1i + ilength a1 ==>
           cm_region_gen region <
             gen + ilength (a0 :: a1)`),
        tail_upper), slots_length);
    ACCEPT_TAC(leaf,
        disj_cases_rule(member, head_result, tail_result));
  }
  return gnode_prove(root);
}
PROOF thm cm_regions_for_slots_gen_upper =
    cm_prove_regions_for_slots_gen_upper();

PROOF static thm cm_prove_regions_for_slots_before(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list)
         (gen:int) (base:int).
         cm_regions_before
           (cm_regions_for_slots structs slots gen base)
           (gen + ilength slots)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_regions_before_def)));
  gnode with_region = GEN_TAC(reduced, "region");
  gnode with_member = DISCH_TAC(with_region, "Hmember");
  ACCEPT_TAC(with_member, match_mp_rule(
      specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `slots:(cm_slot_d)list`,
        `gen:int`, `base:int`, `region:cm_region`),
        cm_regions_for_slots_gen_upper),
      assume_rule(
        `MEM (region:cm_region)
          (cm_regions_for_slots
            (structs:(cm_struct_d)list)
            (slots:(cm_slot_d)list) (gen:int) (base:int))`)));
  return gnode_prove(root);
}
PROOF thm cm_regions_for_slots_before =
    cm_prove_regions_for_slots_before();

PROOF static thm cm_prove_regions_for_slots_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list)
         (gen:int) (base:int) (regions:(cm_region)list).
         cm_region_bases_below_equal
           (cm_regions_for_slots structs slots gen base ++ regions)
           regions gen`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm lower = gen_rule(`region:cm_region`,
      disch_rule(
        `MEM (region:cm_region)
          (cm_regions_for_slots
            (structs:(cm_struct_d)list)
            (slots:(cm_slot_d)list) (gen:int) (base:int))`,
        match_mp_rule(
          specl_rule(TERM_LIST(
            `structs:(cm_struct_d)list`,
            `slots:(cm_slot_d)list`, `gen:int`, `base:int`,
            `region:cm_region`),
            cm_regions_for_slots_gen_lower),
          assume_rule(
            `MEM (region:cm_region)
              (cm_regions_for_slots
                (structs:(cm_struct_d)list)
                (slots:(cm_slot_d)list)
                (gen:int) (base:int))`))));
  ACCEPT_TAC(leaf, match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_regions_for_slots
          (structs:(cm_struct_d)list) (slots:(cm_slot_d)list)
          (gen:int) (base:int)`,
        `regions:(cm_region)list`, `gen:int`),
        cm_region_bases_fresh_append),
      lower));
  return gnode_prove(root);
}
PROOF thm cm_regions_for_slots_bases =
    cm_prove_regions_for_slots_bases();

PROOF static thm cm_prove_regions_before_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(regions:(cm_region)list) (lower:int) (upper:int).
         cm_regions_before regions lower ==>
         lower <= upper ==>
         cm_regions_before regions upper`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm before = conv_rule(rewrite_conv(THM_LIST(
      cm_regions_before_def)), assume_rule(
        `cm_regions_before
          (regions:(cm_region)list) (lower:int)`));
  gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_regions_before_def)));
  gnode with_region = GEN_TAC(reduced, "region");
  gnode with_member = DISCH_TAC(with_region, "Hmember");
  thm old_bound = match_mp_rule(
      spec_rule(`region:cm_region`, before),
      assume_rule(
        `MEM (region:cm_region) (regions:(cm_region)list)`));
  ACCEPT_TAC(with_member, mp_rule(mp_rule(
      int_arith_rule(
        `cm_region_gen (region:cm_region) < (lower:int) ==>
         lower <= (upper:int) ==>
         cm_region_gen region < upper`),
      old_bound), assume_rule(`(lower:int) <= (upper:int)`)));
  return gnode_prove(root);
}
PROOF thm cm_regions_before_mono =
    cm_prove_regions_before_mono();

PROOF static thm cm_prove_regions_for_slots_append_before(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list)
         (gen:int) (base:int) (regions:(cm_region)list).
         cm_regions_before regions gen ==>
         cm_regions_before
           (cm_regions_for_slots structs slots gen base ++ regions)
           (gen + ilength slots)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm fresh_before = specl_rule(TERM_LIST(
      `structs:(cm_struct_d)list`, `slots:(cm_slot_d)list`,
      `gen:int`, `base:int`), cm_regions_for_slots_before);
  thm length_nonnegative = ispec_rule(
      `slots:(cm_slot_d)list`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  thm limits = mp_rule(
      int_arith_rule(
        `0i <= ilength (slots:(cm_slot_d)list) ==>
         (gen:int) <= gen + ilength slots`),
      length_nonnegative);
  thm old_before = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `regions:(cm_region)list`, `gen:int`,
        `(gen:int) + ilength (slots:(cm_slot_d)list)`),
        cm_regions_before_mono),
      assume_rule(
        `cm_regions_before
          (regions:(cm_region)list) (gen:int)`)),
      limits);
  ACCEPT_TAC(leaf, match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_regions_for_slots
          (structs:(cm_struct_d)list) (slots:(cm_slot_d)list)
          (gen:int) (base:int)`,
        `regions:(cm_region)list`,
        `(gen:int) + ilength (slots:(cm_slot_d)list)`),
        cm_regions_before_append),
      fresh_before), old_before));
  return gnode_prove(root);
}
PROOF thm cm_regions_for_slots_append_before =
    cm_prove_regions_for_slots_append_before();

PROOF static thm cm_prove_runtime_stack_regions_for_slots(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (structs:(cm_struct_d)list)
         (slots:(cm_slot_d)list) (gen:int) (base:int)
         (regions:(cm_region)list) (fid:int) (fp:int)
         (cursors:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_regions_before regions gen ==>
         cm_runtime_stack p regions fid fp regions cursors
           spills saved calls ==>
         cm_runtime_stack p
           (cm_regions_for_slots structs slots gen base ++ regions)
           fid fp regions cursors spills saved calls`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm bases = specl_rule(TERM_LIST(
      `structs:(cm_struct_d)list`, `slots:(cm_slot_d)list`,
      `gen:int`, `base:int`, `regions:(cm_region)list`),
      cm_regions_for_slots_bases);
  ACCEPT_TAC(leaf, match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`,
        `cm_regions_for_slots
          (structs:(cm_struct_d)list) (slots:(cm_slot_d)list)
          (gen:int) (base:int) ++ (regions:(cm_region)list)`,
        `regions:(cm_region)list`, `gen:int`,
        `cursors:(cm_acursor)list`, `fid:int`, `fp:int`,
        `regions:(cm_region)list`, `spills:(cm_spill)list`,
        `saved:(cm_spill_frame)list`,
        `calls:(cm_call_sim_frame)list`),
        cm_runtime_stack_below_bases),
      bases), assume_rule(
        `cm_regions_before
          (regions:(cm_region)list) (gen:int)`)),
      assume_rule(
        `cm_runtime_stack (p:cm_program)
          (regions:(cm_region)list) (fid:int) (fp:int)
          regions (cursors:(cm_acursor)list)
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`)));
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_regions_for_slots =
    cm_prove_runtime_stack_regions_for_slots();

PROOF thm cm_region_generations_unique_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_region_generations_unique ([]:(cm_region)list) <=> T) &&
     (!region rest.
        cm_region_generations_unique
          ((region:cm_region) :: (rest:(cm_region)list)) <=>
        (!other. MEM other rest ==>
           ~(cm_region_gen other == cm_region_gen region)) &&
        cm_region_generations_unique rest)`);

PROOF static thm cm_prove_global_regions_generation_bounds(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (globals:(cm_global_d)list)
         (index:int) (region:cm_region).
         MEM region (cm_global_regions p globals index) ==>
         1i + index <= cm_region_gen region &&
         cm_region_gen region <
           1i + index + ilength globals`);
  gnode with_program = GEN_TAC(root, "p");
  thm_list region_rules = THM_LIST(
      get_cm_global_regions_def(), get_theorem_by_name("MEM"));
  gnode_list cases =
      INDUCT_TAC(with_program, `globals:(cm_global_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(region_rules),
        assume_rule(
          `MEM (region:cm_region)
            (cm_global_regions (p:cm_program)
              ([]:(cm_global_d)list) (index:int))`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term head = `CMRegion (cm_global_generation (index:int))
        (cm_global_address (p:cm_program) index) 0i
        (cm_global_size (cm_program_structs p)
          (a0:cm_global_d)) T T`;
    term tail = `cm_global_regions (p:cm_program)
        (a1:(cm_global_d)list) ((index:int) + 1i)`;
    thm member = conv_rule(reduce_rewrite_conv(region_rules),
        assume_rule(
          `MEM (region:cm_region)
            (cm_global_regions (p:cm_program)
              ((a0:cm_global_d) :: (a1:(cm_global_d)list))
              (index:int))`));
    dest_disj_results member_parts = dest_disj(concl(member));
    thm equal = assume_rule(member_parts.tm1);
    thm head_gen = conv_rule(reduce_rewrite_conv(
        get_cm_runtime_defs()),
        ap_term_rule(`cm_region_gen`, equal));
    thm tail_nonnegative = ispec_rule(
        `a1:(cm_global_d)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm slots_length = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        `ilength
          ((a0:cm_global_d) :: (a1:(cm_global_d)list))`);
    thm head_result = mp_rule(mp_rule(mp_rule(
        int_arith_rule(
          `cm_region_gen (region:cm_region) == 1i + (index:int) ==>
           ilength
             ((a0:cm_global_d) :: (a1:(cm_global_d)list)) ==
               1i + ilength a1 ==>
           0i <= ilength a1 ==>
           1i + index <= cm_region_gen region &&
           cm_region_gen region <
             1i + index + ilength (a0 :: a1)`),
        head_gen), slots_length), tail_nonnegative);
    thm ih = specl_rule(TERM_LIST(
        `(index:int) + 1i`, `region:cm_region`),
        cm_invariant_step_assumption(leaf,
          `!(next_index:int) (candidate:cm_region).
             MEM candidate
               (cm_global_regions (p:cm_program)
                 (a1:(cm_global_d)list) next_index) ==>
             1i + next_index <= cm_region_gen candidate &&
             cm_region_gen candidate <
               1i + next_index +
                 ilength (a1:(cm_global_d)list)`));
    thm tail_bounds =
        match_mp_rule(ih, assume_rule(member_parts.tm2));
    thm tail_result = mp_rule(mp_rule(
        int_arith_rule(
          `1i + ((index:int) + 1i) <=
             cm_region_gen (region:cm_region) &&
           cm_region_gen region <
             1i + (index + 1i) +
               ilength (a1:(cm_global_d)list) ==>
           ilength
             ((a0:cm_global_d) :: (a1:(cm_global_d)list)) ==
               1i + ilength a1 ==>
           1i + index <= cm_region_gen region &&
           cm_region_gen region <
             1i + index + ilength (a0 :: a1)`),
        tail_bounds), slots_length);
    ACCEPT_TAC(leaf,
        disj_cases_rule(member, head_result, tail_result));
  }
  return gnode_prove(root);
}
PROOF thm cm_global_regions_generation_bounds =
    cm_prove_global_regions_generation_bounds();

PROOF static thm cm_prove_string_regions_generation_bounds(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (strings:(cm_string_d)list)
         (index:int) (region:cm_region).
         MEM region (cm_string_regions p strings index) ==>
         1i + ilength (cm_program_globals p) + index <=
           cm_region_gen region &&
         cm_region_gen region <
           1i + ilength (cm_program_globals p) +
             index + ilength strings`);
  gnode with_program = GEN_TAC(root, "p");
  thm_list region_rules = THM_LIST(
      get_cm_string_regions_def(), get_theorem_by_name("MEM"));
  gnode_list cases =
      INDUCT_TAC(with_program, `strings:(cm_string_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(region_rules),
        assume_rule(
          `MEM (region:cm_region)
            (cm_string_regions (p:cm_program)
              ([]:(cm_string_d)list) (index:int))`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term head = `CMRegion
        (cm_string_generation (p:cm_program) (index:int))
        (cm_string_address p index) 0i
        (ilength (cm_string_bytes (a0:cm_string_d)) + 1i)
        F T`;
    thm member = conv_rule(reduce_rewrite_conv(region_rules),
        assume_rule(
          `MEM (region:cm_region)
            (cm_string_regions (p:cm_program)
              ((a0:cm_string_d) :: (a1:(cm_string_d)list))
              (index:int))`));
    dest_disj_results member_parts = dest_disj(concl(member));
    thm equal = assume_rule(member_parts.tm1);
    thm head_gen = conv_rule(reduce_rewrite_conv(
        get_cm_runtime_defs()),
        ap_term_rule(`cm_region_gen`, equal));
    thm tail_nonnegative = ispec_rule(
        `a1:(cm_string_d)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm slots_length = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        `ilength
          ((a0:cm_string_d) :: (a1:(cm_string_d)list))`);
    thm head_result = mp_rule(mp_rule(mp_rule(
        int_arith_rule(
          `cm_region_gen (region:cm_region) ==
             1i + ilength (cm_program_globals (p:cm_program)) +
               (index:int) ==>
           ilength
             ((a0:cm_string_d) :: (a1:(cm_string_d)list)) ==
               1i + ilength a1 ==>
           0i <= ilength a1 ==>
           1i + ilength (cm_program_globals p) + index <=
             cm_region_gen region &&
           cm_region_gen region <
             1i + ilength (cm_program_globals p) +
               index + ilength (a0 :: a1)`),
        head_gen), slots_length), tail_nonnegative);
    thm ih = specl_rule(TERM_LIST(
        `(index:int) + 1i`, `region:cm_region`),
        cm_invariant_step_assumption(leaf,
          `!(next_index:int) (candidate:cm_region).
             MEM candidate
               (cm_string_regions (p:cm_program)
                 (a1:(cm_string_d)list) next_index) ==>
             1i + ilength (cm_program_globals p) + next_index <=
               cm_region_gen candidate &&
             cm_region_gen candidate <
               1i + ilength (cm_program_globals p) +
                 next_index + ilength (a1:(cm_string_d)list)`));
    thm tail_bounds =
        match_mp_rule(ih, assume_rule(member_parts.tm2));
    thm tail_result = mp_rule(mp_rule(
        int_arith_rule(
          `1i + ilength (cm_program_globals (p:cm_program)) +
             ((index:int) + 1i) <=
               cm_region_gen (region:cm_region) &&
           cm_region_gen region <
             1i + ilength (cm_program_globals p) +
               (index + 1i) + ilength (a1:(cm_string_d)list) ==>
           ilength
             ((a0:cm_string_d) :: (a1:(cm_string_d)list)) ==
               1i + ilength a1 ==>
           1i + ilength (cm_program_globals p) + index <=
             cm_region_gen region &&
           cm_region_gen region <
             1i + ilength (cm_program_globals p) +
               index + ilength (a0 :: a1)`),
        tail_bounds), slots_length);
    ACCEPT_TAC(leaf,
        disj_cases_rule(member, head_result, tail_result));
  }
  return gnode_prove(root);
}
PROOF thm cm_string_regions_generation_bounds =
    cm_prove_string_regions_generation_bounds();

PROOF static thm cm_prove_global_regions_generations_unique(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (globals:(cm_global_d)list) (index:int).
         cm_region_generations_unique
           (cm_global_regions p globals index)`);
  gnode with_program = GEN_TAC(root, "p");
  gnode_list cases =
      INDUCT_TAC(with_program, `globals:(cm_global_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_global_regions_def(),
        cm_region_generations_unique_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term head = `CMRegion (cm_global_generation (index:int))
        (cm_global_address (p:cm_program) index) 0i
        (cm_global_size (cm_program_structs p)
          (a0:cm_global_d)) T T`;
    term tail = `cm_global_regions (p:cm_program)
        (a1:(cm_global_d)list) ((index:int) + 1i)`;
    thm head_gen = apply_conversion(
        reduce_rewrite_conv(get_cm_runtime_defs()),
        `cm_region_gen ${head:cm_region}`);
    thm tail_distinct = gen_rule(`region:cm_region`,
        disch_rule(
          `MEM (region:cm_region) ${tail:(cm_region)list}`,
          mp_rule(mp_rule(
            int_arith_rule(
              `1i + ((index:int) + 1i) <=
                 cm_region_gen (region:cm_region) ==>
               cm_region_gen ${head:cm_region} == 1i + index ==>
               ~(cm_region_gen region ==
                 cm_region_gen ${head:cm_region})`),
            conjunct1_rule(match_mp_rule(
              specl_rule(TERM_LIST(
                `p:cm_program`, `a1:(cm_global_d)list`,
                `(index:int) + 1i`, `region:cm_region`),
                cm_global_regions_generation_bounds),
              assume_rule(
                `MEM (region:cm_region) ${tail:(cm_region)list}`)))),
            head_gen)));
    thm tail_unique = spec_rule(`(index:int) + 1i`,
        cm_invariant_step_assumption(leaf,
          `!next_index:int.
             cm_region_generations_unique
               (cm_global_regions (p:cm_program)
                 (a1:(cm_global_d)list) next_index)`));
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_global_regions_def(),
        cm_region_generations_unique_def)));
    ACCEPT_TAC(reduced, conj_rule(tail_distinct, tail_unique));
  }
  return gnode_prove(root);
}
PROOF thm cm_global_regions_generations_unique =
    cm_prove_global_regions_generations_unique();

PROOF static thm cm_prove_string_regions_generations_unique(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (strings:(cm_string_d)list) (index:int).
         cm_region_generations_unique
           (cm_string_regions p strings index)`);
  gnode with_program = GEN_TAC(root, "p");
  gnode_list cases =
      INDUCT_TAC(with_program, `strings:(cm_string_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_string_regions_def(),
        cm_region_generations_unique_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term head = `CMRegion
        (cm_string_generation (p:cm_program) (index:int))
        (cm_string_address p index) 0i
        (ilength (cm_string_bytes (a0:cm_string_d)) + 1i)
        F T`;
    term tail = `cm_string_regions (p:cm_program)
        (a1:(cm_string_d)list) ((index:int) + 1i)`;
    thm head_gen = apply_conversion(
        reduce_rewrite_conv(get_cm_runtime_defs()),
        `cm_region_gen ${head:cm_region}`);
    thm tail_distinct = gen_rule(`region:cm_region`,
        disch_rule(
          `MEM (region:cm_region) ${tail:(cm_region)list}`,
          mp_rule(mp_rule(
            int_arith_rule(
              `1i + ilength (cm_program_globals (p:cm_program)) +
                 ((index:int) + 1i) <=
                   cm_region_gen (region:cm_region) ==>
               cm_region_gen ${head:cm_region} ==
                 1i + ilength (cm_program_globals p) + index ==>
               ~(cm_region_gen region ==
                 cm_region_gen ${head:cm_region})`),
            conjunct1_rule(match_mp_rule(
              specl_rule(TERM_LIST(
                `p:cm_program`, `a1:(cm_string_d)list`,
                `(index:int) + 1i`, `region:cm_region`),
                cm_string_regions_generation_bounds),
              assume_rule(
                `MEM (region:cm_region) ${tail:(cm_region)list}`)))),
            head_gen)));
    thm tail_unique = spec_rule(`(index:int) + 1i`,
        cm_invariant_step_assumption(leaf,
          `!next_index:int.
             cm_region_generations_unique
               (cm_string_regions (p:cm_program)
                 (a1:(cm_string_d)list) next_index)`));
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_string_regions_def(),
        cm_region_generations_unique_def)));
    ACCEPT_TAC(reduced, conj_rule(tail_distinct, tail_unique));
  }
  return gnode_prove(root);
}
PROOF thm cm_string_regions_generations_unique =
    cm_prove_string_regions_generations_unique();

PROOF static thm cm_prove_region_generations_unique_append(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:(cm_region)list) (right:(cm_region)list).
         cm_region_generations_unique left ==>
         cm_region_generations_unique right ==>
         (!l r. MEM l left ==> MEM r right ==>
            ~(cm_region_gen l == cm_region_gen r)) ==>
         cm_region_generations_unique (left ++ right)`);
  gnode_list cases =
      INDUCT_TAC(root, `left:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND"))));
    ACCEPT_TAC(reduced, assume_rule(
        `cm_region_generations_unique
          (right:(cm_region)list)`));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm left_unique = conv_rule(rewrite_conv(THM_LIST(
        cm_region_generations_unique_def)), assume_rule(
          `cm_region_generations_unique
            ((a0:cm_region) :: (a1:(cm_region)list))`));
    thm right_unique = assume_rule(
        `cm_region_generations_unique
          (right:(cm_region)list)`);
    thm cross = assume_rule(
        `!l r:cm_region.
           MEM l ((a0:cm_region) :: (a1:(cm_region)list)) ==>
           MEM r (right:(cm_region)list) ==>
           ~(cm_region_gen l == cm_region_gen r)`);
    thm head_member = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(get_theorem_by_name("MEM"))),
        `MEM (a0:cm_region)
          ((a0:cm_region) :: (a1:(cm_region)list))`));
    thm tail_member_unfolded = apply_conversion(
        rewrite_conv(THM_LIST(get_theorem_by_name("MEM"))),
        `MEM (l:cm_region)
          ((a0:cm_region) :: (a1:(cm_region)list))`);
    thm tail_cross = gen_rule(`l:cm_region`,
        gen_rule(`r:cm_region`,
          disch_rule(
            `MEM (l:cm_region) (a1:(cm_region)list)`,
            disch_rule(
              `MEM (r:cm_region) (right:(cm_region)list)`,
              match_mp_rule(match_mp_rule(
                specl_rule(TERM_LIST(
                  `l:cm_region`, `r:cm_region`), cross),
                eq_mp_rule(sym_rule(tail_member_unfolded),
                  disj2_rule(
                    `(l:cm_region) == (a0:cm_region)`,
                    assume_rule(
                      `MEM (l:cm_region)
                        (a1:(cm_region)list)`)))),
                assume_rule(
                  `MEM (r:cm_region)
                    (right:(cm_region)list)`))))));
    thm ih = spec_rule(`right:(cm_region)list`,
        cm_invariant_step_assumption(leaf,
          `!tail_right:(cm_region)list.
             cm_region_generations_unique
               (a1:(cm_region)list) ==>
             cm_region_generations_unique tail_right ==>
             (!l r. MEM l (a1:(cm_region)list) ==>
                MEM r tail_right ==>
                ~(cm_region_gen l == cm_region_gen r)) ==>
             cm_region_generations_unique
               (a1 ++ tail_right)`));
    thm tail_unique = match_mp_rule(match_mp_rule(match_mp_rule(
        ih, conjunct2_rule(left_unique)), right_unique), tail_cross);
    thm right_cross = match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `a0:cm_region`, `other:cm_region`), cross),
        head_member), assume_rule(
          `MEM (other:cm_region) (right:(cm_region)list)`));
    thm right_distinct = not_intro(
        `cm_region_gen (other:cm_region) ==
           cm_region_gen (a0:cm_region)`,
        contra(right_cross, sym_rule(assume_rule(
          `cm_region_gen (other:cm_region) ==
             cm_region_gen (a0:cm_region)`))));
    thm head_distinct = gen_rule(`other:cm_region`,
        disch_rule(
          `MEM (other:cm_region)
            ((a1:(cm_region)list) ++ (right:(cm_region)list))`,
          disj_cases_rule(
            conv_rule(rewrite_conv(THM_LIST(
              get_theorem_by_name("MEM_APPEND"))), assume_rule(
                `MEM (other:cm_region)
                  ((a1:(cm_region)list) ++
                   (right:(cm_region)list))`)),
            match_mp_rule(
              spec_rule(`other:cm_region`,
                conjunct1_rule(left_unique)),
              assume_rule(
                `MEM (other:cm_region)
                  (a1:(cm_region)list)`)),
            right_distinct)));
    thm result = conj_rule(head_distinct, tail_unique);
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND"),
        cm_region_generations_unique_def)));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_region_generations_unique_append =
    cm_prove_region_generations_unique_append();

PROOF static thm cm_prove_static_regions_generations_unique(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_region_generations_unique (cm_static_regions p)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term globals = `cm_global_regions (p:cm_program)
      (cm_program_globals p) 0i`;
  term strings = `cm_string_regions (p:cm_program)
      (cm_program_strings p) 0i`;
  thm global_unique = specl_rule(TERM_LIST(
      `p:cm_program`, `cm_program_globals (p:cm_program)`, `0i`),
      cm_global_regions_generations_unique);
  thm string_unique = specl_rule(TERM_LIST(
      `p:cm_program`, `cm_program_strings (p:cm_program)`, `0i`),
      cm_string_regions_generations_unique);
  thm cross = gen_rule(`global_region:cm_region`,
      gen_rule(`string_region:cm_region`,
        disch_rule(
          `MEM (global_region:cm_region) ${globals:(cm_region)list}`,
          disch_rule(
            `MEM (string_region:cm_region) ${strings:(cm_region)list}`,
            mp_rule(mp_rule(
              int_arith_rule(
                `cm_region_gen (global_region:cm_region) <
                   1i + 0i +
                     ilength (cm_program_globals (p:cm_program)) ==>
                 1i + ilength (cm_program_globals p) + 0i <=
                   cm_region_gen (string_region:cm_region) ==>
                 ~(cm_region_gen global_region ==
                   cm_region_gen string_region)`),
              conjunct2_rule(match_mp_rule(
                specl_rule(TERM_LIST(
                  `p:cm_program`,
                  `cm_program_globals (p:cm_program)`, `0i`,
                  `global_region:cm_region`),
                  cm_global_regions_generation_bounds),
                assume_rule(
                  `MEM (global_region:cm_region)
                    ${globals:(cm_region)list}`)))),
              conjunct1_rule(match_mp_rule(
                specl_rule(TERM_LIST(
                  `p:cm_program`,
                  `cm_program_strings (p:cm_program)`, `0i`,
                  `string_region:cm_region`),
                  cm_string_regions_generation_bounds),
                assume_rule(
                  `MEM (string_region:cm_region)
                    ${strings:(cm_region)list}`))))))));
  thm appended = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        globals, strings), cm_region_generations_unique_append),
      global_unique), string_unique), cross);
  gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_static_regions_def)));
  ACCEPT_TAC(reduced, appended);
  return gnode_prove(root);
}
PROOF thm cm_static_regions_generations_unique =
    cm_prove_static_regions_generations_unique();

PROOF static thm cm_prove_region_base_member_unique(void) {
  gnode root = gnode_new_with_ccl(
      `!(regions:(cm_region)list) (region:cm_region).
         cm_region_generations_unique regions ==>
         MEM region regions ==>
         cm_region_base regions (cm_region_gen region) ==
           cm_region_base_field region`);
  gnode_list cases =
      INDUCT_TAC(root, `regions:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(
        THM_LIST(get_theorem_by_name("MEM"))), assume_rule(
          `MEM (region:cm_region) ([]:(cm_region)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm unique = conv_rule(rewrite_conv(THM_LIST(
        cm_region_generations_unique_def)), assume_rule(
          `cm_region_generations_unique
            ((a0:cm_region) :: (a1:(cm_region)list))`));
    thm member = conv_rule(rewrite_conv(THM_LIST(
        get_theorem_by_name("MEM"))), assume_rule(
          `MEM (region:cm_region)
            ((a0:cm_region) :: (a1:(cm_region)list))`));
    dest_disj_results member_parts = dest_disj(concl(member));
    thm equal = assume_rule(member_parts.tm1);
    thm head_lookup = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(get_cm_runtime_defs()),
        `cm_region_base
           ((a0:cm_region) :: (a1:(cm_region)list))
           (cm_region_gen (a0:cm_region)) ==
         cm_region_base_field a0`));
    thm head_transport = beta_norm(ap_term_rule(
        `\candidate:cm_region.
           cm_region_base
             ((a0:cm_region) :: (a1:(cm_region)list))
             (cm_region_gen candidate) ==
           cm_region_base_field candidate`,
        sym_rule(equal)));
    thm head_result = eq_mp_rule(head_transport, head_lookup);
    thm target_distinct = match_mp_rule(
        spec_rule(`region:cm_region`,
          conjunct1_rule(unique)),
        assume_rule(member_parts.tm2));
    thm head_target_distinct = not_intro(
        `cm_region_gen (a0:cm_region) ==
           cm_region_gen (region:cm_region)`,
        contra(target_distinct, sym_rule(assume_rule(
          `cm_region_gen (a0:cm_region) ==
             cm_region_gen (region:cm_region)`))));
    thm lookup_step = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_region_base_def(), head_target_distinct)),
        `cm_region_base
           ((a0:cm_region) :: (a1:(cm_region)list))
           (cm_region_gen (region:cm_region))`);
    thm ih = spec_rule(`region:cm_region`,
        cm_invariant_step_assumption(leaf,
          `!candidate:cm_region.
             cm_region_generations_unique
               (a1:(cm_region)list) ==>
             MEM candidate (a1:(cm_region)list) ==>
             cm_region_base a1 (cm_region_gen candidate) ==
               cm_region_base_field candidate`));
    thm tail_lookup = match_mp_rule(match_mp_rule(
        ih, conjunct2_rule(unique)),
        assume_rule(member_parts.tm2));
    thm tail_result = trans_rule(lookup_step, tail_lookup);
    ACCEPT_TAC(leaf,
        disj_cases_rule(member, head_result, tail_result));
  }
  return gnode_prove(root);
}
PROOF thm cm_region_base_member_unique =
    cm_prove_region_base_member_unique();

PROOF static thm cm_prove_static_region_base_member(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (region:cm_region).
         MEM region (cm_static_regions p) ==>
         cm_region_base (cm_static_regions p)
           (cm_region_gen region) ==
         cm_region_base_field region`);
  gnode leaf = AUTO_INTROS_TAC(root);
  ACCEPT_TAC(leaf, match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_static_regions (p:cm_program)`, `region:cm_region`),
        cm_region_base_member_unique),
      spec_rule(`p:cm_program`,
        cm_static_regions_generations_unique)),
      assume_rule(
        `MEM (region:cm_region)
          (cm_static_regions (p:cm_program))`)));
  return gnode_prove(root);
}
PROOF thm cm_static_region_base_member =
    cm_prove_static_region_base_member();

PROOF static thm cm_prove_static_regions_before_dynamic(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_regions_before (cm_static_regions p)
           (cm_first_dynamic_generation p)`);
  gnode with_program = GEN_TAC(root, "p");
  gnode reduced = CONV_TAC(with_program, rewrite_conv(THM_LIST(
      cm_regions_before_def, cm_static_regions_def)));
  gnode with_region = GEN_TAC(reduced, "region");
  gnode with_member = DISCH_TAC(with_region, "Hmember");
  thm member = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("MEM_APPEND"))), assume_rule(
        `MEM (region:cm_region)
          (cm_global_regions (p:cm_program)
             (cm_program_globals p) 0i ++
           cm_string_regions p (cm_program_strings p) 0i)`));
  thm global_upper = conjunct2_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `cm_program_globals (p:cm_program)`,
        `0i`, `region:cm_region`),
        cm_global_regions_generation_bounds),
      assume_rule(
        `MEM (region:cm_region)
          (cm_global_regions (p:cm_program)
            (cm_program_globals p) 0i)`)));
  thm string_upper = conjunct2_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `cm_program_strings (p:cm_program)`,
        `0i`, `region:cm_region`),
        cm_string_regions_generation_bounds),
      assume_rule(
        `MEM (region:cm_region)
          (cm_string_regions (p:cm_program)
            (cm_program_strings p) 0i)`)));
  thm strings_nonnegative = ispec_rule(
      `cm_program_strings (p:cm_program)`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  thm global_result = mp_rule(mp_rule(
      int_arith_rule(
        `cm_region_gen (region:cm_region) <
           1i + 0i +
             ilength (cm_program_globals (p:cm_program)) ==>
         0i <= ilength (cm_program_strings p) ==>
         cm_region_gen region <
           1i + ilength (cm_program_globals p) +
             ilength (cm_program_strings p)`),
      global_upper), strings_nonnegative);
  thm string_result = mp_rule(
      int_arith_rule(
        `cm_region_gen (region:cm_region) <
           1i + ilength (cm_program_globals (p:cm_program)) +
             0i + ilength (cm_program_strings p) ==>
         cm_region_gen region <
           1i + ilength (cm_program_globals p) +
             ilength (cm_program_strings p)`),
      string_upper);
  thm result =
      disj_cases_rule(member, global_result, string_result);
  gnode final = CONV_TAC(with_member,
      rewrite_conv(get_cm_runtime_defs()));
  ACCEPT_TAC(final, result);
  return gnode_prove(root);
}
PROOF thm cm_static_regions_before_dynamic =
    cm_prove_static_regions_before_dynamic();

PROOF thm cm_global_sizes_positive_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!structs.
        cm_global_sizes_positive (structs:(cm_struct_d)list)
          ([]:(cm_global_d)list) <=> T) &&
     (!structs global rest.
        cm_global_sizes_positive structs
          ((global:cm_global_d) :: (rest:(cm_global_d)list)) <=>
        0i < cm_global_size structs global &&
        cm_global_sizes_positive structs rest)`);

PROOF static thm cm_prove_global_sizes_positive_total(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (globals:(cm_global_d)list).
         cm_global_sizes_positive structs globals ==>
         0i <= cm_globals_size structs globals`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases =
      INDUCT_TAC(with_structs, `globals:(cm_global_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_globals_size_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm positive = conv_rule(rewrite_conv(THM_LIST(
        cm_global_sizes_positive_def)), assume_rule(
          `cm_global_sizes_positive
            (structs:(cm_struct_d)list)
            ((a0:cm_global_d) :: (a1:(cm_global_d)list))`));
    thm tail_nonnegative = match_mp_rule(
        cm_invariant_step_assumption(leaf,
          `cm_global_sizes_positive
             (structs:(cm_struct_d)list)
             (a1:(cm_global_d)list) ==>
           0i <= cm_globals_size structs a1`),
        conjunct2_rule(positive));
    gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        get_cm_globals_size_def())));
    ACCEPT_TAC(reduced, mp_rule(mp_rule(
        int_arith_rule(
          `0i < cm_global_size
             (structs:(cm_struct_d)list) (a0:cm_global_d) ==>
           0i <= cm_globals_size structs (a1:(cm_global_d)list) ==>
           0i <=
             cm_global_size structs a0 +
               cm_globals_size structs a1`),
        conjunct1_rule(positive)), tail_nonnegative));
  }
  return gnode_prove(root);
}
PROOF thm cm_global_sizes_positive_total =
    cm_prove_global_sizes_positive_total();

PROOF static thm cm_prove_globals_prefix_cell_bounds(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (globals:(cm_global_d)list).
         cm_global_sizes_positive structs globals ==>
         !index. 0i <= index ==> index < ilength globals ==>
           0i <= cm_globals_prefix structs globals index &&
           cm_globals_prefix structs globals index +
             cm_global_size structs (inth index globals) <=
           cm_globals_size structs globals`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases =
      INDUCT_TAC(with_structs, `globals:(cm_global_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(
        THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
        assume_rule(`(index:int) <
          ilength ([]:(cm_global_d)list)`));
    thm contradiction = mp_rule(
        int_arith_rule(
          `0i <= (index:int) ==> index < 0i ==> F`),
        assume_rule(`0i <= (index:int)`));
    CONTR_TAC(leaf, mp_rule(contradiction, impossible));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm positive = conv_rule(rewrite_conv(THM_LIST(
        cm_global_sizes_positive_def)), assume_rule(
          `cm_global_sizes_positive
            (structs:(cm_struct_d)list)
            ((a0:cm_global_d) :: (a1:(cm_global_d)list))`));
    thm tail_total = match_mp_rule(
        specl_rule(TERM_LIST(
          `structs:(cm_struct_d)list`,
          `a1:(cm_global_d)list`),
          cm_global_sizes_positive_total),
        conjunct2_rule(positive));
    gnode_list zero_cases = BOOL_CASES_TAC(
        leaf, `(index:int) == 0i`, "Hindex_zero");
    {
      thm zero = assume_rule(`(index:int) == 0i`);
      thm at_zero = ispecl_rule(TERM_LIST(
          `a0:cm_global_d`, `a1:(cm_global_d)list`),
          cm_inth_zero_cons);
      gnode reduced = CONV_WITH_ASMP_TAC(
          zero_cases[0], reduce_rewrite_conv,
          THM_LIST(get_cm_globals_prefix_def(),
            get_cm_globals_size_def(), zero, at_zero));
      thm inputs = conj_rule(
          conjunct1_rule(positive), tail_total);
      ACCEPT_TAC(reduced, mp_rule(
          int_arith_rule(mk_imp(
            concl(inputs), goal_ccl(reduced->g))),
          inputs));
    }
    {
      thm not_zero = assume_rule(`~((index:int) == 0i)`);
      thm one_le = mp_rule(mp_rule(
          int_arith_rule(
            `0i <= (index:int) ==>
             ~((index:int) == 0i) ==> 1i <= index`),
          assume_rule(`0i <= (index:int)`)), not_zero);
      thm normalized_bound = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            get_theorem_by_name("ILENGTH_DEF"))),
          assume_rule(
            `(index:int) <
              ilength
                ((a0:cm_global_d) :: (a1:(cm_global_d)list))`));
      thm bound_inputs = conj_rule(one_le, normalized_bound);
      thm tail_bounds = mp_rule(int_arith_rule(mk_imp(
          concl(bound_inputs),
          `0i <= (index:int) - 1i &&
           index - 1i < ilength
             (a1:(cm_global_d)list)`)), bound_inputs);
      thm ih = spec_rule(`(index:int) - 1i`,
          match_mp_rule(
            cm_invariant_step_assumption(zero_cases[1],
              `cm_global_sizes_positive
                 (structs:(cm_struct_d)list)
                 (a1:(cm_global_d)list) ==>
               !tail_index.
                 0i <= tail_index ==>
                 tail_index < ilength a1 ==>
                 0i <= cm_globals_prefix structs a1 tail_index &&
                 cm_globals_prefix structs a1 tail_index +
                   cm_global_size structs
                     (inth tail_index a1) <=
                 cm_globals_size structs a1`),
            conjunct2_rule(positive)));
      thm tail_result = match_mp_rule(match_mp_rule(
          ih, conjunct1_rule(tail_bounds)),
          conjunct2_rule(tail_bounds));
      thm at_tail = mp_rule(ispecl_rule(TERM_LIST(
          `a0:cm_global_d`, `a1:(cm_global_d)list`,
          `index:int`), cm_inth_cons_tail), one_le);
      gnode reduced = CONV_WITH_ASMP_TAC(
          zero_cases[1], reduce_rewrite_conv,
          THM_LIST(get_cm_globals_prefix_def(),
            get_cm_globals_size_def(), not_zero, at_tail));
      thm inputs = conj_rule(
          conjunct1_rule(positive), tail_result);
      ACCEPT_TAC(reduced, mp_rule(
          int_arith_rule(mk_imp(
            concl(inputs), goal_ccl(reduced->g))),
          inputs));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_globals_prefix_cell_bounds =
    cm_prove_globals_prefix_cell_bounds();
PROOF static thm cm_prove_global_wf_sizes_positive(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (globals:(cm_global_d)list).
         (!index.
            0i <= index ==> index < ilength globals ==>
            cm_global_wf structs (inth index globals)) ==>
         cm_global_sizes_positive structs globals`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases =
      INDUCT_TAC(with_structs, `globals:(cm_global_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, rewrite_conv(THM_LIST(
        cm_global_sizes_positive_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm all_wf = assume_rule(
        `!index.
           0i <= index ==>
           index <
             ilength
               ((a0:cm_global_d) :: (a1:(cm_global_d)list)) ==>
           cm_global_wf
             (structs:(cm_struct_d)list)
             (inth index (a0 :: a1))`);
    thm tail_length_nonnegative = ispec_rule(
        `a1:(cm_global_d)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm head_bound = by_defs_arith(
        `0i <
          ilength
            ((a0:cm_global_d) :: (a1:(cm_global_d)list))`,
        THM_LIST(get_theorem_by_name("ILENGTH_DEF")),
        THM_LIST(tail_length_nonnegative));
    thm head_wf = match_mp_rule(match_mp_rule(
        spec_rule(`0i`, all_wf),
        int_arith_rule(`0i <= 0i`)), head_bound);
    head_wf = conv_rule(rewrite_conv(THM_LIST(
        ispecl_rule(TERM_LIST(
          `a0:cm_global_d`, `a1:(cm_global_d)list`),
          cm_inth_zero_cons))), head_wf);
    thm head_positive = conv_rule(rewrite_conv(THM_LIST(
        get_cm_global_wf_def())), head_wf);
    gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        cm_global_sizes_positive_def)));
    gnode_list parts = CONJ_TAC(reduced);
    ACCEPT_TAC(parts[0], mp_rule(taut_rule(mk_imp(
        concl(head_positive),
        `0i < cm_global_size
          (structs:(cm_struct_d)list) (a0:cm_global_d)`)),
        head_positive));
    thm ih = cm_invariant_step_assumption(parts[1],
        `(!tail_index.
           0i <= tail_index ==>
           tail_index < ilength (a1:(cm_global_d)list) ==>
           cm_global_wf
             (structs:(cm_struct_d)list)
             (inth tail_index a1)) ==>
         cm_global_sizes_positive structs a1`);
    gnode tail_all_goal = MATCH_MP_TAC(parts[1], ih);
    gnode with_index = GEN_TAC(tail_all_goal, "tail_index");
    gnode tail_leaf = AUTO_INTROS_TAC(with_index);
    thm tail_nonnegative =
        assume_rule(`0i <= (tail_index:int)`);
    thm tail_upper = assume_rule(
        `(tail_index:int) <
          ilength (a1:(cm_global_d)list)`);
    thm full_bounds = conj_rule(
        mp_rule(int_arith_rule(
          `0i <= (tail_index:int) ==>
           0i <= tail_index + 1i`), tail_nonnegative),
        mp_rule(int_arith_rule(mk_imp(
          concl(tail_upper),
          `(tail_index:int) + 1i <
           1i + ilength (a1:(cm_global_d)list)`)),
          tail_upper));
    thm full_upper = eq_mp_rule(sym_rule(
        apply_conversion(reduce_rewrite_conv(THM_LIST(
            get_theorem_by_name("ILENGTH_DEF"))),
          `(tail_index:int) + 1i <
           ilength
             ((a0:cm_global_d) :: (a1:(cm_global_d)list))`)),
        conjunct2_rule(full_bounds));
    thm full_wf = match_mp_rule(match_mp_rule(
        spec_rule(`(tail_index:int) + 1i`, all_wf),
        conjunct1_rule(full_bounds)), full_upper);
    thm one = mp_rule(int_arith_rule(
        `0i <= (tail_index:int) ==>
         1i <= tail_index + 1i`), tail_nonnegative);
    thm at_tail = mp_rule(ispecl_rule(TERM_LIST(
        `a0:cm_global_d`, `a1:(cm_global_d)list`,
        `(tail_index:int) + 1i`),
        cm_inth_cons_tail), one);
    thm tail_index_exact = int_arith_rule(
        `((tail_index:int) + 1i) - 1i == tail_index`);
    ACCEPT_TAC(tail_leaf, conv_rule(
        reduce_rewrite_conv(THM_LIST(at_tail, tail_index_exact)),
        full_wf));
  }
  return gnode_prove(root);
}
PROOF thm cm_global_wf_sizes_positive =
    cm_prove_global_wf_sizes_positive();

PROOF static thm cm_prove_typed_globals_positive(void) {
  gnode root = gnode_new_with_ccl(
      `!p. cm_typed_program p ==>
           cm_global_sizes_positive
             (cm_program_structs p)
             (cm_program_globals p)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm typed = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())),
      assume_rule(`cm_typed_program (p:cm_program)`));
  thm globals_wf = mp_rule(taut_rule(mk_imp(
      concl(typed),
      `!index.
         0i <= index ==>
         index < ilength (cm_program_globals (p:cm_program)) ==>
         cm_global_wf
           (cm_program_structs p)
           (inth index (cm_program_globals p))`)), typed);
  ACCEPT_TAC(leaf, match_mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      `cm_program_globals (p:cm_program)`),
      cm_global_wf_sizes_positive), globals_wf));
  return gnode_prove(root);
}
PROOF thm cm_typed_globals_positive =
    cm_prove_typed_globals_positive();


PROOF static thm cm_prove_strings_size_nonnegative(void) {
  gnode root = gnode_new_with_ccl(
      `!strings:(cm_string_d)list.
         0i <= cm_strings_size strings`);
  gnode_list cases =
      INDUCT_TAC(root, `strings:(cm_string_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_strings_size_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm bytes_nonnegative = ispec_rule(
        `cm_string_bytes (a0:cm_string_d)`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm tail_nonnegative =
        cm_invariant_step_assumption(leaf,
          `0i <= cm_strings_size
            (a1:(cm_string_d)list)`);
    gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        get_cm_strings_size_def())));
    thm inputs = conj_rule(
        bytes_nonnegative, tail_nonnegative);
    ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
        concl(inputs), goal_ccl(reduced->g))), inputs));
  }
  return gnode_prove(root);
}
PROOF thm cm_strings_size_nonnegative =
    cm_prove_strings_size_nonnegative();
PROOF static thm cm_prove_strings_prefix_cell_bounds(void) {
  gnode root = gnode_new_with_ccl(
      `!(strings:(cm_string_d)list) index.
         0i <= index ==> index < ilength strings ==>
         0i <= cm_strings_prefix strings index &&
         cm_strings_prefix strings index +
           ilength (cm_string_bytes (inth index strings)) + 1i <=
         cm_strings_size strings`);
  gnode_list cases =
      INDUCT_TAC(root, `strings:(cm_string_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(
        THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
        assume_rule(`(index:int) <
          ilength ([]:(cm_string_d)list)`));
    CONTR_TAC(leaf, mp_rule(mp_rule(
        int_arith_rule(
          `0i <= (index:int) ==> index < 0i ==> F`),
        assume_rule(`0i <= (index:int)`)), impossible));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm bytes_nonnegative = ispec_rule(
        `cm_string_bytes (a0:cm_string_d)`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm tail_total = spec_rule(
        `a1:(cm_string_d)list`,
        cm_strings_size_nonnegative);
    gnode_list zero_cases = BOOL_CASES_TAC(
        leaf, `(index:int) == 0i`, "Hstring_index_zero");
    {
      thm zero = assume_rule(`(index:int) == 0i`);
      thm at_zero = ispecl_rule(TERM_LIST(
          `a0:cm_string_d`, `a1:(cm_string_d)list`),
          cm_inth_zero_cons);
      gnode reduced = CONV_WITH_ASMP_TAC(
          zero_cases[0], reduce_rewrite_conv,
          THM_LIST(get_cm_strings_prefix_def(),
            get_cm_strings_size_def(), zero, at_zero));
      thm inputs = conj_rule(
          bytes_nonnegative, tail_total);
      ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
          concl(inputs), goal_ccl(reduced->g))), inputs));
    }
    {
      thm not_zero = assume_rule(`~((index:int) == 0i)`);
      thm index_nonnegative =
          assume_rule(`0i <= (index:int)`);
      thm one_le = mp_rule(mp_rule(
          int_arith_rule(
            `0i <= (index:int) ==>
             ~((index:int) == 0i) ==> 1i <= index`),
          index_nonnegative), not_zero);
      thm normalized_bound = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            get_theorem_by_name("ILENGTH_DEF"))),
          assume_rule(
            `(index:int) <
              ilength
                ((a0:cm_string_d) :: (a1:(cm_string_d)list))`));
      thm bound_inputs = conj_rule(one_le, normalized_bound);
      thm tail_bounds = mp_rule(int_arith_rule(mk_imp(
          concl(bound_inputs),
          `0i <= (index:int) - 1i &&
           index - 1i < ilength
             (a1:(cm_string_d)list)`)), bound_inputs);
      thm ih = spec_rule(`(index:int) - 1i`,
          cm_invariant_step_assumption(zero_cases[1],
            `!tail_index.
               0i <= tail_index ==>
               tail_index < ilength
                 (a1:(cm_string_d)list) ==>
               0i <= cm_strings_prefix a1 tail_index &&
               cm_strings_prefix a1 tail_index +
                 ilength
                   (cm_string_bytes
                     (inth tail_index a1)) +
                 1i <=
               cm_strings_size a1`));
      thm tail_result = match_mp_rule(match_mp_rule(
          ih, conjunct1_rule(tail_bounds)),
          conjunct2_rule(tail_bounds));
      thm at_tail = mp_rule(ispecl_rule(TERM_LIST(
          `a0:cm_string_d`, `a1:(cm_string_d)list`,
          `index:int`), cm_inth_cons_tail), one_le);
      gnode reduced = CONV_WITH_ASMP_TAC(
          zero_cases[1], reduce_rewrite_conv,
          THM_LIST(get_cm_strings_prefix_def(),
            get_cm_strings_size_def(), not_zero, at_tail));
      thm inputs = conj_rule(bytes_nonnegative, tail_result);
      ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
          concl(inputs), goal_ccl(reduced->g))), inputs));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_strings_prefix_cell_bounds =
    cm_prove_strings_prefix_cell_bounds();

PROOF static thm cm_prove_global_region_member_index(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (globals:(cm_global_d)list).
         !start region.
           MEM region (cm_global_regions p globals start) ==>
           ?offset.
             0i <= offset &&
             offset < ilength globals &&
             region ==
               CMRegion
                 (cm_global_generation (start + offset))
                 (cm_global_address p (start + offset)) 0i
                 (cm_global_size (cm_program_structs p)
                   (inth offset globals)) T T`);
  gnode with_program = GEN_TAC(root, "p");
  gnode_list cases =
      INDUCT_TAC(with_program, `globals:(cm_global_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_global_regions_def(),
        get_theorem_by_name("MEM"))),
        assume_rule(
          `MEM (region:cm_region)
            (cm_global_regions (p:cm_program)
              ([]:(cm_global_d)list) (start:int))`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm member = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_global_regions_def(),
        get_theorem_by_name("MEM"))),
        assume_rule(
          `MEM (region:cm_region)
            (cm_global_regions (p:cm_program)
              ((a0:cm_global_d) :: (a1:(cm_global_d)list))
              (start:int))`));
    dest_disj_results parts = dest_disj(concl(member));
    thm head_equal = assume_rule(parts.tm1);
    thm tail_length_nonnegative = ispec_rule(
        `a1:(cm_global_d)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm start_zero = int_arith_rule(
        `(start:int) + 0i == start`);
    thm head_at = ispecl_rule(TERM_LIST(
        `a0:cm_global_d`, `a1:(cm_global_d)list`),
        cm_inth_zero_cons);
    term wanted =
        `?offset.
           0i <= offset &&
           offset <
             ilength
               ((a0:cm_global_d) :: (a1:(cm_global_d)list)) &&
           (region:cm_region) ==
             CMRegion
               (cm_global_generation ((start:int) + offset))
               (cm_global_address (p:cm_program) (start + offset))
               0i
               (cm_global_size (cm_program_structs p)
                 (inth offset (a0 :: a1))) T T`;
    thm head_body = by_defs_arith(
        `0i <= 0i &&
         0i <
           ilength
             ((a0:cm_global_d) :: (a1:(cm_global_d)list)) &&
         (region:cm_region) ==
           CMRegion
             (cm_global_generation ((start:int) + 0i))
             (cm_global_address (p:cm_program) (start + 0i))
             0i
             (cm_global_size (cm_program_structs p)
               (inth 0i (a0 :: a1))) T T`,
        THM_LIST(get_theorem_by_name("ILENGTH_DEF"),
          start_zero, head_at, head_equal),
        THM_LIST(tail_length_nonnegative));
    thm head_result = exists_rule(wanted, `0i`, head_body);

    thm ih = specl_rule(TERM_LIST(
        `(start:int) + 1i`, `region:cm_region`),
        cm_invariant_step_assumption(leaf,
          `!next_start candidate.
             MEM candidate
               (cm_global_regions (p:cm_program)
                 (a1:(cm_global_d)list) next_start) ==>
             ?offset.
               0i <= offset &&
               offset < ilength a1 &&
               candidate ==
                 CMRegion
                   (cm_global_generation
                     (next_start + offset))
                   (cm_global_address p
                     (next_start + offset)) 0i
                   (cm_global_size (cm_program_structs p)
                     (inth offset a1)) T T`));
    thm tail_exists = match_mp_rule(
        ih, assume_rule(parts.tm2));
    term tail_body_term =
        `0i <= (offset:int) &&
         offset < ilength (a1:(cm_global_d)list) &&
         (region:cm_region) ==
           CMRegion
             (cm_global_generation
               (((start:int) + 1i) + offset))
             (cm_global_address (p:cm_program)
               ((start + 1i) + offset)) 0i
             (cm_global_size (cm_program_structs p)
               (inth offset a1)) T T`;
    thm tail_body = assume_rule(tail_body_term);
    thm offset_lower = mp_rule(taut_rule(mk_imp(
        concl(tail_body), `0i <= (offset:int)`)), tail_body);
    thm offset_upper = mp_rule(taut_rule(mk_imp(
        concl(tail_body),
        `(offset:int) <
          ilength (a1:(cm_global_d)list)`)), tail_body);
    thm region_equal = mp_rule(taut_rule(mk_imp(
        concl(tail_body),
        `(region:cm_region) ==
          CMRegion
            (cm_global_generation
              (((start:int) + 1i) + offset))
            (cm_global_address (p:cm_program)
              ((start + 1i) + offset)) 0i
            (cm_global_size (cm_program_structs p)
              (inth offset a1)) T T`)), tail_body);
    thm new_lower = mp_rule(int_arith_rule(
        `0i <= (offset:int) ==>
         0i <= offset + 1i`), offset_lower);
    thm new_upper = by_defs_arith(
        `(offset:int) + 1i <
          ilength
            ((a0:cm_global_d) :: (a1:(cm_global_d)list))`,
        THM_LIST(get_theorem_by_name("ILENGTH_DEF")),
        THM_LIST(offset_upper));
    thm one = mp_rule(int_arith_rule(
        `0i <= (offset:int) ==>
         1i <= offset + 1i`), offset_lower);
    thm at_tail = mp_rule(ispecl_rule(TERM_LIST(
        `a0:cm_global_d`, `a1:(cm_global_d)list`,
        `(offset:int) + 1i`),
        cm_inth_cons_tail), one);
    thm offset_exact = int_arith_rule(
        `((offset:int) + 1i) - 1i == offset`);
    at_tail = conv_rule(reduce_rewrite_conv(
        THM_LIST(offset_exact)), at_tail);
    thm index_exact = int_ring_rule(
        `((start:int) + 1i) + (offset:int) ==
         start + (offset + 1i)`);
    thm new_equal = conv_rule(rewrite_conv(THM_LIST(
        index_exact, sym_rule(at_tail))), region_equal);
    thm new_body = conj_rule(new_lower,
        conj_rule(new_upper, new_equal));
    thm tail_witness = exists_rule(
        wanted, `(offset:int) + 1i`, new_body);
    thm tail_result = choose_rule(
        `offset:int`, tail_exists, tail_witness);
    ACCEPT_TAC(leaf,
        disj_cases_rule(member, head_result, tail_result));
  }
  return gnode_prove(root);
}
PROOF thm cm_global_region_member_index =
    cm_prove_global_region_member_index();

PROOF static thm cm_prove_string_region_member_index(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (strings:(cm_string_d)list).
         !start region.
           MEM region (cm_string_regions p strings start) ==>
           ?offset.
             0i <= offset &&
             offset < ilength strings &&
             region ==
               CMRegion
                 (cm_string_generation p (start + offset))
                 (cm_string_address p (start + offset)) 0i
                 (ilength
                   (cm_string_bytes (inth offset strings)) + 1i)
                 F T`);
  gnode with_program = GEN_TAC(root, "p");
  gnode_list cases =
      INDUCT_TAC(with_program, `strings:(cm_string_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_string_regions_def(),
        get_theorem_by_name("MEM"))),
        assume_rule(
          `MEM (region:cm_region)
            (cm_string_regions (p:cm_program)
              ([]:(cm_string_d)list) (start:int))`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm member = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_string_regions_def(),
        get_theorem_by_name("MEM"))),
        assume_rule(
          `MEM (region:cm_region)
            (cm_string_regions (p:cm_program)
              ((a0:cm_string_d) :: (a1:(cm_string_d)list))
              (start:int))`));
    dest_disj_results parts = dest_disj(concl(member));
    thm head_equal = assume_rule(parts.tm1);
    thm tail_length_nonnegative = ispec_rule(
        `a1:(cm_string_d)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm start_zero = int_arith_rule(
        `(start:int) + 0i == start`);
    thm head_at = ispecl_rule(TERM_LIST(
        `a0:cm_string_d`, `a1:(cm_string_d)list`),
        cm_inth_zero_cons);
    term wanted =
        `?offset.
           0i <= offset &&
           offset <
             ilength
               ((a0:cm_string_d) :: (a1:(cm_string_d)list)) &&
           (region:cm_region) ==
             CMRegion
               (cm_string_generation
                 (p:cm_program) ((start:int) + offset))
               (cm_string_address p (start + offset)) 0i
               (ilength
                 (cm_string_bytes (inth offset (a0 :: a1))) + 1i)
               F T`;
    thm head_body = by_defs_arith(
        `0i <= 0i &&
         0i <
           ilength
             ((a0:cm_string_d) :: (a1:(cm_string_d)list)) &&
         (region:cm_region) ==
           CMRegion
             (cm_string_generation
               (p:cm_program) ((start:int) + 0i))
             (cm_string_address p (start + 0i)) 0i
             (ilength
               (cm_string_bytes (inth 0i (a0 :: a1))) + 1i)
             F T`,
        THM_LIST(get_theorem_by_name("ILENGTH_DEF"),
          start_zero, head_at, head_equal),
        THM_LIST(tail_length_nonnegative));
    thm head_result = exists_rule(wanted, `0i`, head_body);

    thm ih = specl_rule(TERM_LIST(
        `(start:int) + 1i`, `region:cm_region`),
        cm_invariant_step_assumption(leaf,
          `!next_start candidate.
             MEM candidate
               (cm_string_regions (p:cm_program)
                 (a1:(cm_string_d)list) next_start) ==>
             ?offset.
               0i <= offset &&
               offset < ilength a1 &&
               candidate ==
                 CMRegion
                   (cm_string_generation p
                     (next_start + offset))
                   (cm_string_address p
                     (next_start + offset)) 0i
                   (ilength
                     (cm_string_bytes
                       (inth offset a1)) + 1i)
                   F T`));
    thm tail_exists = match_mp_rule(
        ih, assume_rule(parts.tm2));
    term tail_body_term =
        `0i <= (offset:int) &&
         offset < ilength (a1:(cm_string_d)list) &&
         (region:cm_region) ==
           CMRegion
             (cm_string_generation
               (p:cm_program) (((start:int) + 1i) + offset))
             (cm_string_address p
               ((start + 1i) + offset)) 0i
             (ilength
               (cm_string_bytes (inth offset a1)) + 1i)
             F T`;
    thm tail_body = assume_rule(tail_body_term);
    thm offset_lower = mp_rule(taut_rule(mk_imp(
        concl(tail_body), `0i <= (offset:int)`)), tail_body);
    thm offset_upper = mp_rule(taut_rule(mk_imp(
        concl(tail_body),
        `(offset:int) <
          ilength (a1:(cm_string_d)list)`)), tail_body);
    thm region_equal = mp_rule(taut_rule(mk_imp(
        concl(tail_body),
        `(region:cm_region) ==
          CMRegion
            (cm_string_generation
              (p:cm_program) (((start:int) + 1i) + offset))
            (cm_string_address p
              ((start + 1i) + offset)) 0i
            (ilength
              (cm_string_bytes (inth offset a1)) + 1i)
            F T`)), tail_body);
    thm new_lower = mp_rule(int_arith_rule(
        `0i <= (offset:int) ==>
         0i <= offset + 1i`), offset_lower);
    thm new_upper = by_defs_arith(
        `(offset:int) + 1i <
          ilength
            ((a0:cm_string_d) :: (a1:(cm_string_d)list))`,
        THM_LIST(get_theorem_by_name("ILENGTH_DEF")),
        THM_LIST(offset_upper));
    thm one = mp_rule(int_arith_rule(
        `0i <= (offset:int) ==>
         1i <= offset + 1i`), offset_lower);
    thm at_tail = mp_rule(ispecl_rule(TERM_LIST(
        `a0:cm_string_d`, `a1:(cm_string_d)list`,
        `(offset:int) + 1i`),
        cm_inth_cons_tail), one);
    thm offset_exact = int_arith_rule(
        `((offset:int) + 1i) - 1i == offset`);
    at_tail = conv_rule(reduce_rewrite_conv(
        THM_LIST(offset_exact)), at_tail);
    thm index_exact = int_ring_rule(
        `((start:int) + 1i) + (offset:int) ==
         start + (offset + 1i)`);
    thm new_equal = conv_rule(rewrite_conv(THM_LIST(
        index_exact, sym_rule(at_tail))), region_equal);
    thm new_body = conj_rule(new_lower,
        conj_rule(new_upper, new_equal));
    thm tail_witness = exists_rule(
        wanted, `(offset:int) + 1i`, new_body);
    thm tail_result = choose_rule(
        `offset:int`, tail_exists, tail_witness);
    ACCEPT_TAC(leaf,
        disj_cases_rule(member, head_result, tail_result));
  }
  return gnode_prove(root);
}
PROOF thm cm_string_region_member_index =
    cm_prove_string_region_member_index();

PROOF static thm cm_prove_global_static_region_geometry(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (region:cm_region).
         cm_typed_program p ==>
         MEM region
           (cm_global_regions p (cm_program_globals p) 0i) ==>
         0i <= cm_region_lo region &&
         cm_region_lo region <= cm_region_hi region &&
         16i <= cm_region_base_field region +
           cm_region_lo region &&
         cm_region_base_field region +
           cm_region_hi region <= cm_static_size p`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm typed_assumption =
      assume_rule(`cm_typed_program (p:cm_program)`);
  thm typed = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), typed_assumption);
  thm globals_wf = mp_rule(taut_rule(mk_imp(
      concl(typed),
      `!index.
         0i <= index ==>
         index < ilength (cm_program_globals (p:cm_program)) ==>
         cm_global_wf
           (cm_program_structs p)
           (inth index (cm_program_globals p))`)), typed);
  thm indexed = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `cm_program_globals (p:cm_program)`,
      `0i`, `region:cm_region`),
      cm_global_region_member_index),
      assume_rule(
        `MEM (region:cm_region)
          (cm_global_regions (p:cm_program)
            (cm_program_globals p) 0i)`));
  term indexed_body_term =
      `0i <= (offset:int) &&
       offset < ilength (cm_program_globals (p:cm_program)) &&
       (region:cm_region) ==
         CMRegion
           (cm_global_generation (0i + offset))
           (cm_global_address p (0i + offset)) 0i
           (cm_global_size (cm_program_structs p)
             (inth offset (cm_program_globals p))) T T`;
  thm indexed_body = assume_rule(indexed_body_term);
  thm offset_lower = mp_rule(taut_rule(mk_imp(
      concl(indexed_body), `0i <= (offset:int)`)), indexed_body);
  thm offset_upper = mp_rule(taut_rule(mk_imp(
      concl(indexed_body),
      `(offset:int) <
        ilength (cm_program_globals (p:cm_program))`)),
      indexed_body);
  thm region_equal = mp_rule(taut_rule(mk_imp(
      concl(indexed_body),
      `(region:cm_region) ==
        CMRegion
          (cm_global_generation (0i + (offset:int)))
          (cm_global_address (p:cm_program) (0i + offset)) 0i
          (cm_global_size (cm_program_structs p)
            (inth offset (cm_program_globals p))) T T`)),
      indexed_body);
  thm zero_offset = int_arith_rule(
      `0i + (offset:int) == offset`);
  region_equal = conv_rule(rewrite_conv(
      THM_LIST(zero_offset)), region_equal);
  thm wf_at = match_mp_rule(match_mp_rule(
      spec_rule(`offset:int`, globals_wf),
      offset_lower), offset_upper);
  thm wf_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_global_wf_def())), wf_at);
  thm size_positive = mp_rule(taut_rule(mk_imp(
      concl(wf_open),
      `0i < cm_global_size
        (cm_program_structs (p:cm_program))
        (inth (offset:int) (cm_program_globals p))`)),
      wf_open);
  thm positive = match_mp_rule(
      spec_rule(`p:cm_program`, cm_typed_globals_positive),
      typed_assumption);
  thm prefix_bounds = match_mp_rule(match_mp_rule(
      spec_rule(`offset:int`,
        match_mp_rule(specl_rule(TERM_LIST(
          `cm_program_structs (p:cm_program)`,
          `cm_program_globals (p:cm_program)`),
          cm_globals_prefix_cell_bounds), positive)),
      offset_lower), offset_upper);
  thm strings_nonnegative = spec_rule(
      `cm_program_strings (p:cm_program)`,
      cm_strings_size_nonnegative);
  term descriptor =
      `CMRegion
         (cm_global_generation (offset:int))
         (cm_global_address (p:cm_program) offset) 0i
         (cm_global_size (cm_program_structs p)
           (inth offset (cm_program_globals p))) T T`;
  term descriptor_property =
      `0i <= cm_region_lo ${descriptor:cm_region} &&
       cm_region_lo ${descriptor:cm_region} <=
         cm_region_hi ${descriptor:cm_region} &&
       16i <= cm_region_base_field ${descriptor:cm_region} +
         cm_region_lo ${descriptor:cm_region} &&
       cm_region_base_field ${descriptor:cm_region} +
         cm_region_hi ${descriptor:cm_region} <=
       cm_static_size (p:cm_program)`;
  thm numeric = conj_rule(size_positive,
      conj_rule(prefix_bounds, strings_nonnegative));
  thm normalized = apply_conversion(then_conv(
      reduce_rewrite_conv(get_cm_runtime_defs()),
      reduce_rewrite_conv(THM_LIST(
        get_cm_global_address_def(),
        get_cm_static_size_def()))), descriptor_property);
  struct dest_eq_results normalized_parts =
      dest_eq(concl(normalized));
  thm normalized_result = mp_rule(int_arith_rule(mk_imp(
      concl(numeric), normalized_parts.tm2)), numeric);
  thm descriptor_result =
      eq_mp_rule(sym_rule(normalized), normalized_result);
  thm transported = eq_mp_rule(sym_rule(beta_norm(ap_term_rule(
      `\candidate:cm_region.
         0i <= cm_region_lo candidate &&
         cm_region_lo candidate <= cm_region_hi candidate &&
         16i <= cm_region_base_field candidate +
           cm_region_lo candidate &&
         cm_region_base_field candidate +
           cm_region_hi candidate <= cm_static_size (p:cm_program)`,
      region_equal))), descriptor_result);
  thm result = choose_rule(
      `offset:int`, indexed, transported);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_global_static_region_geometry =
    cm_prove_global_static_region_geometry();
PROOF static thm cm_prove_string_static_region_geometry(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (region:cm_region).
         cm_typed_program p ==>
         MEM region
           (cm_string_regions p (cm_program_strings p) 0i) ==>
         0i <= cm_region_lo region &&
         cm_region_lo region <= cm_region_hi region &&
         16i <= cm_region_base_field region +
           cm_region_lo region &&
         cm_region_base_field region +
           cm_region_hi region <= cm_static_size p`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm typed_assumption =
      assume_rule(`cm_typed_program (p:cm_program)`);
  thm indexed = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `cm_program_strings (p:cm_program)`,
      `0i`, `region:cm_region`),
      cm_string_region_member_index),
      assume_rule(
        `MEM (region:cm_region)
          (cm_string_regions (p:cm_program)
            (cm_program_strings p) 0i)`));
  term indexed_body_term =
      `0i <= (offset:int) &&
       offset < ilength (cm_program_strings (p:cm_program)) &&
       (region:cm_region) ==
         CMRegion
           (cm_string_generation p (0i + offset))
           (cm_string_address p (0i + offset)) 0i
           (ilength
             (cm_string_bytes
               (inth offset (cm_program_strings p))) + 1i)
           F T`;
  thm indexed_body = assume_rule(indexed_body_term);
  thm offset_lower = mp_rule(taut_rule(mk_imp(
      concl(indexed_body), `0i <= (offset:int)`)), indexed_body);
  thm offset_upper = mp_rule(taut_rule(mk_imp(
      concl(indexed_body),
      `(offset:int) <
        ilength (cm_program_strings (p:cm_program))`)),
      indexed_body);
  thm region_equal = mp_rule(taut_rule(mk_imp(
      concl(indexed_body),
      `(region:cm_region) ==
        CMRegion
          (cm_string_generation
            (p:cm_program) (0i + (offset:int)))
          (cm_string_address p (0i + offset)) 0i
          (ilength
            (cm_string_bytes
              (inth offset (cm_program_strings p))) + 1i)
          F T`)), indexed_body);
  thm zero_offset = int_arith_rule(
      `0i + (offset:int) == offset`);
  region_equal = conv_rule(rewrite_conv(
      THM_LIST(zero_offset)), region_equal);
  thm bytes_nonnegative = ispec_rule(
      `cm_string_bytes
        (inth (offset:int)
          (cm_program_strings (p:cm_program)))`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  thm prefix_bounds = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_program_strings (p:cm_program)`,
        `offset:int`), cm_strings_prefix_cell_bounds),
      offset_lower), offset_upper);
  thm globals_positive = match_mp_rule(
      spec_rule(`p:cm_program`, cm_typed_globals_positive),
      typed_assumption);
  thm globals_nonnegative = match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`,
        `cm_program_globals (p:cm_program)`),
        cm_global_sizes_positive_total),
      globals_positive);
  term descriptor =
      `CMRegion
         (cm_string_generation (p:cm_program) (offset:int))
         (cm_string_address p offset) 0i
         (ilength
           (cm_string_bytes
             (inth offset (cm_program_strings p))) + 1i)
         F T`;
  term descriptor_property =
      `0i <= cm_region_lo ${descriptor:cm_region} &&
       cm_region_lo ${descriptor:cm_region} <=
         cm_region_hi ${descriptor:cm_region} &&
       16i <= cm_region_base_field ${descriptor:cm_region} +
         cm_region_lo ${descriptor:cm_region} &&
       cm_region_base_field ${descriptor:cm_region} +
         cm_region_hi ${descriptor:cm_region} <=
       cm_static_size (p:cm_program)`;
  thm numeric = conj_rule(bytes_nonnegative,
      conj_rule(prefix_bounds, globals_nonnegative));
  thm normalized = apply_conversion(then_conv(
      reduce_rewrite_conv(get_cm_runtime_defs()),
      reduce_rewrite_conv(THM_LIST(
        get_cm_string_address_def(),
        get_cm_static_size_def()))), descriptor_property);
  struct dest_eq_results normalized_parts =
      dest_eq(concl(normalized));
  thm normalized_result = mp_rule(int_arith_rule(mk_imp(
      concl(numeric), normalized_parts.tm2)), numeric);
  thm descriptor_result =
      eq_mp_rule(sym_rule(normalized), normalized_result);
  thm transported = eq_mp_rule(sym_rule(beta_norm(ap_term_rule(
      `\candidate:cm_region.
         0i <= cm_region_lo candidate &&
         cm_region_lo candidate <= cm_region_hi candidate &&
         16i <= cm_region_base_field candidate +
           cm_region_lo candidate &&
         cm_region_base_field candidate +
           cm_region_hi candidate <= cm_static_size (p:cm_program)`,
      region_equal))), descriptor_result);
  thm result = choose_rule(
      `offset:int`, indexed, transported);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_string_static_region_geometry =
    cm_prove_string_static_region_geometry();

PROOF static thm cm_prove_typed_static_regions_layout(void) {
  gnode root = gnode_new_with_ccl(
      `!p. cm_typed_program p ==>
           cm_static_regions_layout p (cm_static_regions p)`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_typed = DISCH_TAC(with_program, "Htyped");
  gnode unfolded = CONV_TAC(with_typed, rewrite_conv(THM_LIST(
      cm_static_regions_layout_def)));
  gnode with_region = GEN_TAC(unfolded, "region");
  gnode leaf = AUTO_INTROS_TAC(with_region);
  thm premise = assume_rule(
      `MEM (region:cm_region)
         (cm_static_regions (p:cm_program)) &&
       cm_region_live region`);
  thm member = mp_rule(taut_rule(mk_imp(
      concl(premise),
      `MEM (region:cm_region)
        (cm_static_regions (p:cm_program))`)), premise);
  thm member_split = conv_rule(rewrite_conv(THM_LIST(
      cm_static_regions_def,
      get_theorem_by_name("MEM_APPEND"))), member);
  dest_disj_results parts = dest_disj(concl(member_split));
  thm base_lookup = match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `region:cm_region`),
        cm_static_region_base_member), member);
  thm typed = assume_rule(`cm_typed_program (p:cm_program)`);
  thm global_geometry = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `region:cm_region`),
        cm_global_static_region_geometry), typed),
      assume_rule(parts.tm1));
  thm string_geometry = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `region:cm_region`),
        cm_string_static_region_geometry), typed),
      assume_rule(parts.tm2));
  thm global_result = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(base_lookup))), global_geometry);
  thm string_result = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(base_lookup))), string_geometry);
  ACCEPT_TAC(leaf, disj_cases_rule(
      member_split, global_result, string_result));
  return gnode_prove(root);
}
PROOF thm cm_typed_static_regions_layout =
    cm_prove_typed_static_regions_layout();

PROOF static thm cm_prove_runtime_stack_halt_initial(void) {
  gnode root = gnode_new_with_ccl(
      `!p. cm_typed_program p ==>
           cm_runtime_stack p (cm_static_regions p) (--1i) 1048576i
             (cm_static_regions p)
             [CMACursor CAHaltP 0i 0i 0i]
             [] [] []`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm typed_assumption =
      assume_rule(`cm_typed_program (p:cm_program)`);
  thm typed = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), typed_assumption);
  thm bounds = mp_rule(taut_rule(mk_imp(
      concl(typed),
      `16i <= cm_static_size (p:cm_program) &&
       cm_static_size p <= 1048576i`)), typed);
  thm dead = spec_rule(
      `cm_static_regions (p:cm_program)`,
      cm_region_dead_prefix_refl);
  thm layout = match_mp_rule(
      spec_rule(`p:cm_program`,
        cm_typed_static_regions_layout),
      typed_assumption);
  thm facts = conj_rule(dead, conj_rule(bounds, layout));
  conv phase_reduction = then_conv(
      reduce_rewrite_conv(get_cm_runtime_defs()),
      reduce_rewrite_conv(THM_LIST(
        cm_cursor_phase_def,
        cm_phase_is_call_def,
        cm_phase_is_scope_def,
        cm_phase_is_halt_def)));
  thm not_call = eqt_elim_rule(apply_conversion(
      phase_reduction,
      `~cm_phase_is_call
        (cm_cursor_phase
          (CMACursor CAHaltP 0i 0i 0i))`));
  thm not_scope = eqt_elim_rule(apply_conversion(
      phase_reduction,
      `~cm_phase_is_scope
        (cm_cursor_phase
          (CMACursor CAHaltP 0i 0i 0i))`));
  thm is_halt = eqt_elim_rule(apply_conversion(
      phase_reduction,
      `cm_phase_is_halt
        (cm_cursor_phase
          (CMACursor CAHaltP 0i 0i 0i))`));
  gnode reduced = CONV_TAC(leaf,
      reduce_rewrite_conv(THM_LIST(
        cm_runtime_stack_def,
        not_call, not_scope, is_halt)));
  ACCEPT_TAC(reduced, mp_rule(taut_rule(mk_imp(
      concl(facts), goal_ccl(reduced->g))), facts));
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_halt_initial =
    cm_prove_runtime_stack_halt_initial();
PROOF static int cmc_preservation_invariant_step_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==


      _cmc_preservation_invariant_step_axioms_before,
      "cmc_preservation_invariant_step introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_invariant_step_checks =
    cmc_preservation_invariant_step_final_checks();
