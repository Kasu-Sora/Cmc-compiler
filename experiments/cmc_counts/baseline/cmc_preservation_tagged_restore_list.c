#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_tagged_restore_list.h"
#include "cmc_preservation_invariant_step.h"

#require "cmc_sim.c"
#require "cmc_preservation_invariant_step.c"

PROOF static size_t _cmc_preservation_tagged_restore_list_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_restore_tagged_source(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(active:(cm_region)list).
         !(all:(cm_region)list) (old:(cm_region)list)
           (tagged:int->bool) (addr:int).
         cm_restore_tagged all active old tagged addr ==>
         tagged addr`);
  gnode_list cases = INDUCT_TAC(root_node, `active:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm restored = assume_rule(
        `cm_restore_tagged (all:(cm_region)list)
          ([]:(cm_region)list) (old:(cm_region)list)
          (tagged:int->bool) (addr:int)`);
    restored = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_restore_tagged_def())), restored);
    ACCEPT_TAC(leaf, restored);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term active = `(a0:cm_region) :: (a1:(cm_region)list)`;
    term boundary = `${active:(cm_region)list} ==
        (old:(cm_region)list)`;
    gnode_list boundary_cases = BOOL_CASES_TAC(
        leaf, boundary, "Hboundary");
    {
      thm restored = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_restore_tagged_def(), assume_rule(boundary))),
          assume_rule(
            `cm_restore_tagged (all:(cm_region)list)
              ${active:(cm_region)list} (old:(cm_region)list)
              (tagged:int->bool) (addr:int)`));
      ACCEPT_TAC(boundary_cases[0], restored);
    }
    {
      thm not_boundary = assume_rule(mk_not(boundary));
      term next_tagged =
          `if cm_region_live (a0:cm_region)
           then cm_clear_tagged (tagged:int->bool)
             (cm_region_base (all:(cm_region)list)
                (cm_region_gen a0) + cm_region_lo a0)
             (cm_region_hi a0 - cm_region_lo a0)
           else tagged`;
      thm tail_restored = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_restore_tagged_def(), not_boundary)), assume_rule(
            `cm_restore_tagged (all:(cm_region)list)
              ${active:(cm_region)list} (old:(cm_region)list)
              (tagged:int->bool) (addr:int)`));
      thm ih = specl_rule(TERM_LIST(
          `all:(cm_region)list`, `old:(cm_region)list`,
          next_tagged, `addr:int`),
          assume_rule(goal_lasmps(boundary_cases[1]->g)[0].tm));
      thm next_value = mp_rule(ih, tail_restored);
      gnode_list live_cases = BOOL_CASES_TAC(boundary_cases[1],
          `cm_region_live (a0:cm_region)`, "Hlive");
      {
        thm old_value = conv_rule(reduce_rewrite_conv(THM_LIST(
            assume_rule(`cm_region_live (a0:cm_region)`),
            get_cm_clear_tagged_def())), next_value);
        ACCEPT_TAC(live_cases[0], conjunct1_rule(old_value));
      }
      {
        thm old_value = conv_rule(reduce_rewrite_conv(THM_LIST(
            assume_rule(`~cm_region_live (a0:cm_region)`))),
            next_value);
        ACCEPT_TAC(live_cases[1], old_value);
      }
    }
  }
  return gnode_prove(root_node);
}
PROOF thm cm_restore_tagged_source =
    cm_prove_restore_tagged_source();

PROOF static thm cm_prove_restore_tagged_keeps_region(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(active:(cm_region)list).
         !(all:(cm_region)list) (old:(cm_region)list)
           (tagged:int->bool) (addr:int) (byte:int)
           (region:cm_region).
         MEM region active ==>
         cm_region_live region ==>
         cm_region_base all (cm_region_gen region) +
             cm_region_lo region <= byte &&
           byte < cm_region_base all (cm_region_gen region) +
             cm_region_hi region ==>
         addr <= byte && byte < addr + 8i ==>
         cm_restore_tagged all active old tagged addr ==>
         MEM region (cm_restore_regions active old) &&
           cm_region_live region`);
  gnode_list cases = INDUCT_TAC(root_node, `active:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("MEM"))), assume_rule(
          `MEM (region:cm_region) ([]:(cm_region)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term active = `(a0:cm_region) :: (a1:(cm_region)list)`;
    term boundary = `${active:(cm_region)list} ==
        (old:(cm_region)list)`;
    thm member = assume_rule(
        `MEM (region:cm_region) ${active:(cm_region)list}`);
    thm region_live = assume_rule(
        `cm_region_live (region:cm_region)`);
    thm region_bounds = assume_rule(
        `cm_region_base (all:(cm_region)list)
             (cm_region_gen (region:cm_region)) +
             cm_region_lo region <= (byte:int) &&
         byte < cm_region_base all (cm_region_gen region) +
             cm_region_hi region`);
    thm byte_bounds = assume_rule(
        `(addr:int) <= (byte:int) && byte < addr + 8i`);
    thm restored_tag = assume_rule(
        `cm_restore_tagged (all:(cm_region)list)
          ${active:(cm_region)list} (old:(cm_region)list)
          (tagged:int->bool) (addr:int)`);
    gnode_list boundary_cases = BOOL_CASES_TAC(
        leaf, boundary, "Hboundary");
    {
      thm boundary_fact = assume_rule(boundary);
      thm member_old = conv_rule(
          rewrite_conv(THM_LIST(boundary_fact)), member);
      thm restored_member = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_restore_regions_def(), boundary_fact, member_old)),
          `MEM (region:cm_region)
            (cm_restore_regions ${active:(cm_region)list}
              (old:(cm_region)list))`));
      ACCEPT_TAC(boundary_cases[0],
          conj_rule(restored_member, region_live));
    }
    {
      thm not_boundary = assume_rule(mk_not(boundary));
      term next_tagged =
          `if cm_region_live (a0:cm_region)
           then cm_clear_tagged (tagged:int->bool)
             (cm_region_base (all:(cm_region)list)
                (cm_region_gen a0) + cm_region_lo a0)
             (cm_region_hi a0 - cm_region_lo a0)
           else tagged`;
      thm tail_restored = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_restore_tagged_def(), not_boundary)), restored_tag);
      thm member_cases = conv_rule(rewrite_conv(THM_LIST(
          get_theorem_by_name("MEM"))), member);
      struct dest_disj_results alternatives = dest_disj(
          concl(member_cases));
      thm head_equal = assume_rule(alternatives.tm1);
      thm tail_member = assume_rule(alternatives.tm2);

      thm head_live = conv_rule(rewrite_conv(THM_LIST(head_equal)),
          region_live);
      thm head_bounds = conv_rule(rewrite_conv(THM_LIST(head_equal)),
          region_bounds);
      thm tail_source = specl_rule(TERM_LIST(
          `a1:(cm_region)list`, `all:(cm_region)list`,
          `old:(cm_region)list`, next_tagged, `addr:int`),
          cm_restore_tagged_source);
      thm next_value = mp_rule(tail_source, tail_restored);
      thm clear_value = conv_rule(reduce_rewrite_conv(THM_LIST(
          head_live, get_cm_clear_tagged_def())), next_value);
      thm no_overlap = conjunct2_rule(clear_value);
      thm overlaps = mp_rule(mp_rule(int_arith_rule(
          `(cm_region_base (all:(cm_region)list)
               (cm_region_gen (a0:cm_region)) + cm_region_lo a0 <=
               (byte:int) &&
             byte < cm_region_base all (cm_region_gen a0) +
               cm_region_hi a0) ==>
           ((addr:int) <= byte && byte < addr + 8i) ==>
           0i < cm_region_hi a0 - cm_region_lo a0 &&
           addr <
               (cm_region_base all (cm_region_gen a0) +
                cm_region_lo a0) +
               (cm_region_hi a0 - cm_region_lo a0) &&
           cm_region_base all (cm_region_gen a0) +
               cm_region_lo a0 < addr + 8i`),
          head_bounds), byte_bounds);
      thm head_false = contra(no_overlap, overlaps);
      term wanted =
          `MEM (region:cm_region)
             (cm_restore_regions ${active:(cm_region)list}
               (old:(cm_region)list)) &&
           cm_region_live region`;
      thm head_result = false_elim_rule(head_false, wanted);

      thm ih = specl_rule(TERM_LIST(
          `all:(cm_region)list`, `old:(cm_region)list`, next_tagged,
          `addr:int`, `byte:int`, `region:cm_region`),
          assume_rule(goal_lasmps(boundary_cases[1]->g)[0].tm));
      ih = match_mp_rule(ih, tail_member);
      ih = match_mp_rule(ih, region_live);
      ih = match_mp_rule(ih, region_bounds);
      ih = match_mp_rule(ih, byte_bounds);
      ih = match_mp_rule(ih, tail_restored);
      thm tail_kept = conjunct1_rule(ih);
      thm restored_member = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_restore_regions_def(), not_boundary, tail_kept,
            get_theorem_by_name("MEM"))),
          `MEM (region:cm_region)
            (cm_restore_regions ${active:(cm_region)list}
              (old:(cm_region)list))`));
      thm tail_result = conj_rule(restored_member,
          conjunct2_rule(ih));
      ACCEPT_TAC(boundary_cases[1], disj_cases_rule(
          member_cases, head_result, tail_result));
    }
  }
  return gnode_prove(root_node);
}
PROOF thm cm_restore_tagged_keeps_region =
    cm_prove_restore_tagged_keeps_region();

PROOF static thm cm_prove_restore_live_region_source(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(active:(cm_region)list).
         !(p:cm_program) (all:(cm_region)list)
           (fid:int) (fp:int) (old:(cm_region)list)
           (region:cm_region).
         cm_region_prefix_safe p all fid fp active old ==>
         MEM region (cm_restore_regions active old) ==>
         cm_region_live region ==>
         MEM region active`);
  gnode_list cases = INDUCT_TAC(root_node, `active:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm prefix = conv_rule(rewrite_conv(THM_LIST(
        cm_region_prefix_safe_def)), assume_rule(
          `cm_region_prefix_safe (p:cm_program)
            (all:(cm_region)list) (fid:int) (fp:int)
            ([]:(cm_region)list) (old:(cm_region)list)`));
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_restore_regions_def(), prefix,
        get_theorem_by_name("MEM"))), assume_rule(
          `MEM (region:cm_region)
            (cm_restore_regions ([]:(cm_region)list)
              (old:(cm_region)list))`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term active = `(a0:cm_region) :: (a1:(cm_region)list)`;
    term boundary = `${active:(cm_region)list} ==
        (old:(cm_region)list)`;
    thm prefix = assume_rule(
        `cm_region_prefix_safe (p:cm_program)
          (all:(cm_region)list) (fid:int) (fp:int)
          ${active:(cm_region)list} (old:(cm_region)list)`);
    thm restored_member = assume_rule(
        `MEM (region:cm_region)
          (cm_restore_regions ${active:(cm_region)list}
            (old:(cm_region)list))`);
    thm region_live = assume_rule(
        `cm_region_live (region:cm_region)`);
    gnode_list boundary_cases = BOOL_CASES_TAC(
        leaf, boundary, "Hboundary");
    {
      thm boundary_fact = assume_rule(boundary);
      thm member_old = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_restore_regions_def(), boundary_fact)),
          restored_member);
      thm member_active = conv_rule(rewrite_conv(THM_LIST(
          sym_rule(boundary_fact))), member_old);
      ACCEPT_TAC(boundary_cases[0], member_active);
    }
    {
      thm not_boundary = assume_rule(mk_not(boundary));
      thm opened_prefix = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_region_prefix_safe_def, not_boundary)), prefix);
      thm tail_prefix = conjunct2_rule(opened_prefix);
      thm member_cases = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_restore_regions_def(), not_boundary,
          get_theorem_by_name("MEM"))), restored_member);
      struct dest_disj_results alternatives = dest_disj(
          concl(member_cases));
      thm retired_equal = assume_rule(alternatives.tm1);
      thm tail_member = assume_rule(alternatives.tm2);
      thm retired_live = conv_rule(
          rewrite_conv(THM_LIST(retired_equal)), region_live);
      thm head_false = contra(
          spec_rule(`a0:cm_region`, cm_retire_region_dead),
          retired_live);
      thm head_result = false_elim_rule(head_false,
          `MEM (region:cm_region) ${active:(cm_region)list}`);

      thm ih = specl_rule(TERM_LIST(
          `p:cm_program`, `all:(cm_region)list`,
          `fid:int`, `fp:int`, `old:(cm_region)list`,
          `region:cm_region`),
          assume_rule(goal_lasmps(boundary_cases[1]->g)[0].tm));
      ih = match_mp_rule(ih, tail_prefix);
      ih = match_mp_rule(ih, tail_member);
      ih = match_mp_rule(ih, region_live);
      thm tail_result = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_theorem_by_name("MEM"), ih)),
          `MEM (region:cm_region) ${active:(cm_region)list}`));
      ACCEPT_TAC(boundary_cases[1], disj_cases_rule(
          member_cases, head_result, tail_result));
    }
  }
  return gnode_prove(root_node);
}
PROOF thm cm_restore_live_region_source =
    cm_prove_restore_live_region_source();

PROOF static int cmc_preservation_tagged_restore_list_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_tagged_restore_list_axioms_before,
      "cmc_preservation_tagged_restore_list introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_restore_tagged_source)) == 0,
      "restore tagged-source theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_restore_tagged_keeps_region)) == 0,
      "restore tagged-region theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_tagged_restore_list_checks =
    cmc_preservation_tagged_restore_list_final_checks();
