#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_tagged_allocation.h"

#require "cmc_preservation_tagged.c"
#require "cmc_preservation_invariant_step.c"

PROOF static size_t _cmc_preservation_tagged_allocation_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_live_span_forward(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(left:cm_src_state) (right:cm_src_state)
         (base:int) (width:int).
         (!addr. cm_live_address left addr ==>
           cm_live_address right addr) ==>
         cm_live_span left base width ==>
         cm_live_span right base width`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  thm forward = assume_rule(
      `!addr:int. cm_live_address (left:cm_src_state) addr ==>
        cm_live_address (right:cm_src_state) addr`);
  thm old_span = conv_rule(rewrite_conv(THM_LIST(
      cm_live_span_def)), assume_rule(
        `cm_live_span (left:cm_src_state) (base:int) (width:int)`));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_live_span_def)));
  gnode at_address = AUTO_INTROS_TAC(opened);
  thm old_live = mp_rule(spec_rule(`addr:int`, old_span),
      assume_rule(
        `(base:int) <= (addr:int) && addr < base + (width:int)`));
  ACCEPT_TAC(at_address, mp_rule(spec_rule(`addr:int`, forward),
      old_live));
  return gnode_prove(root_node);
}
PROOF thm cm_live_span_forward = cm_prove_live_span_forward();

PROOF static thm cm_prove_tagged_span_clear_extension(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(left:cm_src_state) (right:cm_src_state)
         (base:int) (width:int).
         (!addr. cm_state_tagged right addr <=>
           cm_clear_tagged (cm_state_tagged left) base width addr) ==>
         (!addr. cm_live_address right addr ==>
           cm_live_address left addr ||
           (base <= addr && addr < base + width)) ==>
         (!addr. cm_live_address left addr ==>
           cm_live_address right addr) ==>
         cm_tagged_span_valid left ==>
         cm_tagged_span_valid right`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  thm tagged_equal = assume_rule(
      `!addr:int. cm_state_tagged (right:cm_src_state) addr <=>
        cm_clear_tagged (cm_state_tagged (left:cm_src_state))
          (base:int) (width:int) addr`);
  thm classify = assume_rule(
      `!addr:int. cm_live_address (right:cm_src_state) addr ==>
        cm_live_address (left:cm_src_state) addr ||
        ((base:int) <= addr && addr < base + (width:int))`);
  thm forward = assume_rule(
      `!addr:int. cm_live_address (left:cm_src_state) addr ==>
        cm_live_address (right:cm_src_state) addr`);
  thm old_valid = conv_rule(rewrite_conv(THM_LIST(
      cm_tagged_span_valid_def)), assume_rule(
        `cm_tagged_span_valid (left:cm_src_state)`));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_tagged_span_valid_def)));
  gnode at_address = AUTO_INTROS_TAC(opened);
  thm new_parts = assume_rule(
      `cm_state_tagged (right:cm_src_state) (addr:int) &&
       cm_live_address right addr`);
  thm cleared = eq_mp_rule(spec_rule(`addr:int`, tagged_equal),
      conjunct1_rule(new_parts));
  thm clear_parts = conv_rule(rewrite_conv(THM_LIST(
      get_cm_clear_tagged_def())), cleared);
  thm live_cases = mp_rule(spec_rule(`addr:int`, classify),
      conjunct2_rule(new_parts));
  struct dest_disj_results alternatives = dest_disj(concl(live_cases));
  thm old_live = assume_rule(alternatives.tm1);
  thm local_live = assume_rule(alternatives.tm2);
  thm old_span = mp_rule(spec_rule(`addr:int`, old_valid),
      conj_rule(conjunct1_rule(clear_parts), old_live));
  thm retained = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `left:cm_src_state`, `right:cm_src_state`, `addr:int`, `8i`),
      cm_live_span_forward), forward), old_span);
  thm overlap = mp_rule(int_arith_rule(mk_imp(concl(local_live),
      `0i < (width:int) &&
       (addr:int) < (base:int) + width &&
       base < addr + 8i`)), local_live);
  thm impossible = contra(conjunct2_rule(clear_parts), overlap);
  thm local_result = false_elim_rule(impossible,
      `cm_live_span (right:cm_src_state) (addr:int) 8i`);
  ACCEPT_TAC(at_address,
      disj_cases_rule(live_cases, retained, local_result));
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_clear_extension =
    cm_prove_tagged_span_clear_extension();

PROOF static term cm_local_region_term(void) {
  return `CMRegion (cm_state_nextgen (st:cm_src_state))
      (cm_local_base (p:cm_program) (fid:int) (slot:int)
        (cm_state_fp st)) 0i
      (cm_slot_size (cm_program_structs p)
        (inth slot (cm_function_locals
          (inth fid (cm_program_functions p))))) T T`;
}

PROOF static thm cm_prove_activate_live_old(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (slot:int) (st:cm_src_state)
         (addr:int).
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         cm_live_address st addr ==>
         cm_live_address (cm_activate_local p fid slot st) addr`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  term old_regions = `cm_state_regions (st:cm_src_state)`;
  term nextgen = `cm_state_nextgen (st:cm_src_state)`;
  term fresh = cm_local_region_term();
  term all_regions = `${fresh:cm_region} :: ${old_regions:(cm_region)list}`;
  thm before = assume_rule(
      `cm_regions_before ${old_regions:(cm_region)list} ${nextgen:int}`);
  thm before_open = conv_rule(rewrite_conv(THM_LIST(
      cm_regions_before_def)), before);
  thm fresh_generation_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_region_gen_def())),
      `${nextgen:int} <= cm_region_gen ${fresh:cm_region}`);
  thm fresh_generation = eq_mp_rule(sym_rule(fresh_generation_view),
      int_arith_rule(`${nextgen:int} <= ${nextgen:int}`));
  thm bases = match_mp_rule(specl_rule(TERM_LIST(
      fresh, old_regions, nextgen), cm_region_bases_fresh_cons),
      fresh_generation);
  bases = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_region_bases_below_equal_def, get_cm_region_gen_def())), bases);
  thm old_exists = conv_rule(rewrite_conv(THM_LIST(
      cm_live_address_def)), assume_rule(
        `cm_live_address (st:cm_src_state) (addr:int)`));
  thm old_body = assume_rule(
      `MEM (region:cm_region) ${old_regions:(cm_region)list} &&
       cm_region_live region &&
       cm_region_base ${old_regions:(cm_region)list}
           (cm_region_gen region) + cm_region_lo region <= (addr:int) &&
       addr < cm_region_base ${old_regions:(cm_region)list}
           (cm_region_gen region) + cm_region_hi region`);
  thm member = conjunct1_rule(old_body);
  thm gen_bound = match_mp_rule(spec_rule(
      `region:cm_region`, before_open), member);
  thm base_equal = match_mp_rule(spec_rule(
      `cm_region_gen (region:cm_region)`, bases), gen_bound);
  thm old_bounds = conjunct2_rule(conjunct2_rule(old_body));
  thm new_bounds = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(base_equal))), old_bounds);
  thm new_member = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_theorem_by_name("MEM"),
        member)),
      `MEM (region:cm_region) ${all_regions:(cm_region)list}`));
  thm new_body = conj_rule(new_member, conj_rule(
      conjunct1_rule(conjunct2_rule(old_body)), new_bounds));
  thm new_exists = exists_rule(
      `?candidate.
         MEM candidate ${all_regions:(cm_region)list} &&
         cm_region_live candidate &&
         cm_region_base ${all_regions:(cm_region)list}
             (cm_region_gen candidate) + cm_region_lo candidate <=
           (addr:int) &&
         addr < cm_region_base ${all_regions:(cm_region)list}
             (cm_region_gen candidate) + cm_region_hi candidate`,
      `region:cm_region`, new_body);
  thm selected = choose_rule(`region:cm_region`, old_exists, new_exists);
  term target_live =
      `cm_live_address
        (cm_activate_local (p:cm_program) (fid:int) (slot:int)
          (st:cm_src_state)) (addr:int)`;
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_activate_local_def());
  vector_add(&rules, cm_live_address_def);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), target_live);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), selected));
  return gnode_prove(root_node);
}
PROOF thm cm_activate_live_old = cm_prove_activate_live_old();

PROOF static thm cm_prove_activate_live_old_or_local(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (slot:int) (st:cm_src_state)
         (addr:int).
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         cm_live_address (cm_activate_local p fid slot st) addr ==>
         cm_live_address st addr ||
         (cm_local_base p fid slot (cm_state_fp st) <= addr &&
          addr < cm_local_base p fid slot (cm_state_fp st) +
            cm_slot_size (cm_program_structs p)
              (inth slot (cm_function_locals
                (inth fid (cm_program_functions p)))))`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  term old_regions = `cm_state_regions (st:cm_src_state)`;
  term nextgen = `cm_state_nextgen (st:cm_src_state)`;
  term fresh = cm_local_region_term();
  term all_regions = `${fresh:cm_region} :: ${old_regions:(cm_region)list}`;
  term local_base =
      `cm_local_base (p:cm_program) (fid:int) (slot:int)
        (cm_state_fp (st:cm_src_state))`;
  term local_width =
      `cm_slot_size (cm_program_structs (p:cm_program))
        (inth (slot:int) (cm_function_locals
          (inth (fid:int) (cm_program_functions p))))`;
  thm before = assume_rule(
      `cm_regions_before ${old_regions:(cm_region)list} ${nextgen:int}`);
  thm before_open = conv_rule(rewrite_conv(THM_LIST(
      cm_regions_before_def)), before);
  thm fresh_generation_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_region_gen_def())),
      `${nextgen:int} <= cm_region_gen ${fresh:cm_region}`);
  thm fresh_generation = eq_mp_rule(sym_rule(fresh_generation_view),
      int_arith_rule(`${nextgen:int} <= ${nextgen:int}`));
  thm bases = match_mp_rule(specl_rule(TERM_LIST(
      fresh, old_regions, nextgen), cm_region_bases_fresh_cons),
      fresh_generation);
  bases = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_region_bases_below_equal_def, get_cm_region_gen_def())), bases);
  thm_list state_rules = get_cm_state_core_defs();
  vector_add(&state_rules, get_cm_activate_local_def());
  thm new_exists = conv_rule(reduce_rewrite_conv(state_rules),
      conv_rule(rewrite_conv(THM_LIST(cm_live_address_def)),
        assume_rule(
          `cm_live_address
            (cm_activate_local (p:cm_program) (fid:int) (slot:int)
              (st:cm_src_state)) (addr:int)`)));
  thm new_body = assume_rule(
      `MEM (region:cm_region) ${all_regions:(cm_region)list} &&
       cm_region_live region &&
       cm_region_base ${all_regions:(cm_region)list}
           (cm_region_gen region) + cm_region_lo region <= (addr:int) &&
       addr < cm_region_base ${all_regions:(cm_region)list}
           (cm_region_gen region) + cm_region_hi region`);
  thm member_cases = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("MEM"))), conjunct1_rule(new_body));
  struct dest_disj_results members = dest_disj(concl(member_cases));
  thm fresh_equal = assume_rule(members.tm1);
  thm old_member = assume_rule(members.tm2);

  thm fresh_bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
      fresh_equal, get_cm_region_base_def(), get_cm_region_gen_def(),
      get_cm_region_lo_def(), get_cm_region_hi_def(),
      get_cm_region_base_field_def())),
      conjunct2_rule(conjunct2_rule(new_body)));
  thm fresh_result = disj2_rule(
      `cm_live_address (st:cm_src_state) (addr:int)`, fresh_bounds);
  fresh_result = conv_rule(rewrite_conv(THM_LIST(
      int_ring_rule(`!z:int. z + 0i == z`))), fresh_result);

  thm gen_bound = match_mp_rule(spec_rule(
      `region:cm_region`, before_open), old_member);
  thm base_equal = match_mp_rule(spec_rule(
      `cm_region_gen (region:cm_region)`, bases), gen_bound);
  thm old_bounds = conv_rule(rewrite_conv(THM_LIST(
      base_equal)), conjunct2_rule(conjunct2_rule(new_body)));
  thm old_body = conj_rule(old_member, conj_rule(
      conjunct1_rule(conjunct2_rule(new_body)), old_bounds));
  thm old_exists = exists_rule(
      `?candidate.
         MEM candidate ${old_regions:(cm_region)list} &&
         cm_region_live candidate &&
         cm_region_base ${old_regions:(cm_region)list}
             (cm_region_gen candidate) + cm_region_lo candidate <=
           (addr:int) &&
         addr < cm_region_base ${old_regions:(cm_region)list}
             (cm_region_gen candidate) + cm_region_hi candidate`,
      `region:cm_region`, old_body);
  thm old_live = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_live_address_def)),
      `cm_live_address (st:cm_src_state) (addr:int)`)), old_exists);
  thm old_result = disj1_rule(old_live,
      `${local_base:int} <= (addr:int) &&
       addr < ${local_base:int} + ${local_width:int}`);
  thm classified = disj_cases_rule(member_cases,
      fresh_result, old_result);
  thm selected = choose_rule(`region:cm_region`, new_exists, classified);
  ACCEPT_TAC(leaf, selected);
  return gnode_prove(root_node);
}
PROOF thm cm_activate_live_old_or_local =
    cm_prove_activate_live_old_or_local();

PROOF static thm cm_prove_tagged_span_activate_local(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (slot:int) (st:cm_src_state).
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         cm_tagged_span_valid st ==>
         cm_tagged_span_valid (cm_activate_local p fid slot st)`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  term local_base =
      `cm_local_base (p:cm_program) (fid:int) (slot:int)
        (cm_state_fp (st:cm_src_state))`;
  term local_width =
      `cm_slot_size (cm_program_structs (p:cm_program))
        (inth (slot:int) (cm_function_locals
          (inth (fid:int) (cm_program_functions p))))`;
  term activated =
      `cm_activate_local (p:cm_program) (fid:int) (slot:int)
        (st:cm_src_state)`;
  thm before = assume_rule(
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`);
  thm_list tagged_rules = get_cm_state_core_defs();
  vector_add(&tagged_rules, get_cm_activate_local_def());
  thm tagged_equal = apply_conversion(
      reduce_rewrite_conv(tagged_rules),
      `!addr:int.
         cm_state_tagged ${activated:cm_src_state} addr <=>
         cm_clear_tagged (cm_state_tagged st)
           ${local_base:int} ${local_width:int} addr`);
  tagged_equal = eqt_elim_rule(tagged_equal);
  thm classify = gen_rule(`addr:int`, disch_rule(
      `cm_live_address ${activated:cm_src_state} (addr:int)`,
      match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `slot:int`, `st:cm_src_state`,
        `addr:int`), cm_activate_live_old_or_local), before),
        assume_rule(
          `cm_live_address ${activated:cm_src_state} (addr:int)`))));
  thm forward = gen_rule(`addr:int`, disch_rule(
      `cm_live_address (st:cm_src_state) (addr:int)`,
      match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `slot:int`, `st:cm_src_state`,
        `addr:int`), cm_activate_live_old), before),
        assume_rule(
          `cm_live_address (st:cm_src_state) (addr:int)`))));
  thm result = specl_rule(TERM_LIST(
      `st:cm_src_state`, activated, local_base, local_width),
      cm_tagged_span_clear_extension);
  result = match_mp_rule(result, tagged_equal);
  result = match_mp_rule(result, classify);
  result = match_mp_rule(result, forward);
  result = match_mp_rule(result, assume_rule(
      `cm_tagged_span_valid (st:cm_src_state)`));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_activate_local =
    cm_prove_tagged_span_activate_local();

PROOF static int cmc_preservation_tagged_allocation_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_tagged_allocation_axioms_before,
      "cmc_preservation_tagged_allocation introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_live_span_forward)) == 0,
      "live-span forward theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_clear_extension)) == 0,
      "tagged clear-extension theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_activate_live_old)) == 0,
      "activate old-live theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_activate_live_old_or_local)) == 0,
      "activate live classification theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_activate_local)) == 0,
      "activate tagged-span theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_tagged_allocation_checks =
    cmc_preservation_tagged_allocation_final_checks();
