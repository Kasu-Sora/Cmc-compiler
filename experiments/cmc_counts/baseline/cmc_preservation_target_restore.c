#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_restore.h"
#include "cmc_preservation_invariant_step.h"
#include "cmc_preservation_tagged_restore_list.h"
#include "cmc_preservation_call_transport.h"

#require "cmc_preservation_target_machine.c"
#require "cmc_preservation_invariant_step.c"
#require "cmc_preservation_tagged_restore_list.c"
#require "cmc_preservation_call_transport.c"

PROOF static size_t _cmc_preservation_target_restore_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_restore_target_consequence(
    const thm premise, const term conclusion) {
  return mp_rule(taut_rule(mk_imp(concl(premise), conclusion)), premise);
}
PROOF static thm cm_prove_region_bases_equal_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:(cm_region)list) (right:(cm_region)list) (limit:int).
         cm_region_bases_equal left right ==>
         cm_region_bases_below_equal left right limit`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm all = conv_rule(rewrite_conv(THM_LIST(
      cm_region_bases_equal_def)), assume_rule(
        `cm_region_bases_equal (left:(cm_region)list)
          (right:(cm_region)list)`));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_region_bases_below_equal_def)));
  gnode point = AUTO_INTROS_TAC(opened);
  ACCEPT_TAC(point, spec_rule(`gen:int`, all));
  return gnode_prove(root);
}
PROOF static thm cm_region_bases_equal_below =
    cm_prove_region_bases_equal_below();


PROOF static thm cm_prove_restore_init_source(void) {
  gnode root = gnode_new_with_ccl(
      `!(active:(cm_region)list).
         !(all:(cm_region)list) (old:(cm_region)list)
           (init:int->bool) (addr:int).
         cm_restore_init all active old init addr ==>
         init addr`);
  gnode_list cases = INDUCT_TAC(root, `active:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm restored = assume_rule(
        `cm_restore_init (all:(cm_region)list)
          ([]:(cm_region)list) (old:(cm_region)list)
          (init:int->bool) (addr:int)`);
    restored = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_restore_init_def())), restored);
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
          get_cm_restore_init_def(), assume_rule(boundary))),
          assume_rule(
            `cm_restore_init (all:(cm_region)list)
              ${active:(cm_region)list} (old:(cm_region)list)
              (init:int->bool) (addr:int)`));
      ACCEPT_TAC(boundary_cases[0], restored);
    }
    {
      thm not_boundary = assume_rule(mk_not(boundary));
      term next_init =
          `if cm_region_live (a0:cm_region)
           then cm_clear_init (init:int->bool)
             (cm_region_base (all:(cm_region)list)
                (cm_region_gen a0) + cm_region_lo a0)
             (cm_region_hi a0 - cm_region_lo a0)
           else init`;
      thm tail_restored = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_restore_init_def(), not_boundary)), assume_rule(
            `cm_restore_init (all:(cm_region)list)
              ${active:(cm_region)list} (old:(cm_region)list)
              (init:int->bool) (addr:int)`));
      thm ih = specl_rule(TERM_LIST(
          `all:(cm_region)list`, `old:(cm_region)list`,
          next_init, `addr:int`),
          assume_rule(goal_lasmps(boundary_cases[1]->g)[0].tm));
      thm next_value = mp_rule(ih, tail_restored);
      gnode_list live_cases = BOOL_CASES_TAC(boundary_cases[1],
          `cm_region_live (a0:cm_region)`, "Hlive");
      {
        thm old_value = conv_rule(reduce_rewrite_conv(THM_LIST(
            assume_rule(`cm_region_live (a0:cm_region)`),
            get_cm_clear_init_def())), next_value);
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
  return gnode_prove(root);
}
PROOF static thm cm_restore_init_source =
    cm_prove_restore_init_source();

PROOF static thm cm_prove_restore_tagged_init_lockstep(void) {
  gnode root = gnode_new_with_ccl(
      `!(active:(cm_region)list).
         !(p:cm_program) (all:(cm_region)list) (fid:int) (fp:int)
           (old:(cm_region)list) (init:int->bool)
           (tagged:int->bool) (addr:int).
         cm_region_prefix_safe p all fid fp active old ==>
         cm_restore_tagged all active old tagged addr ==>
         init addr ==>
         cm_restore_init all active old init addr`);
  gnode_list cases = INDUCT_TAC(root, `active:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        cm_region_prefix_safe_def, get_cm_restore_tagged_def(),
        get_cm_restore_init_def()));
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
    thm restored_tagged = assume_rule(
        `cm_restore_tagged (all:(cm_region)list)
          ${active:(cm_region)list} (old:(cm_region)list)
          (tagged:int->bool) (addr:int)`);
    thm old_init = assume_rule(`(init:int->bool) (addr:int)`);
    gnode_list boundary_cases = BOOL_CASES_TAC(
        leaf, boundary, "Hboundary");
    {
      gnode reduced = CONV_WITH_ASMP_TAC(
          boundary_cases[0], reduce_rewrite_conv, THM_LIST(
            get_cm_restore_init_def(), assume_rule(boundary)));
      if (IS_NULL(reduced->solved)) {
        ACCEPT_TAC(reduced, old_init);
      }
    }
    {
      thm not_boundary = assume_rule(mk_not(boundary));
      thm opened_prefix = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_region_prefix_safe_def, not_boundary)), prefix);
      thm head_safe = conjunct1_rule(opened_prefix);
      thm tail_prefix = conjunct2_rule(opened_prefix);
      term base =
          `cm_region_base (all:(cm_region)list)
             (cm_region_gen (a0:cm_region)) + cm_region_lo a0`;
      term width =
          `cm_region_hi (a0:cm_region) - cm_region_lo a0`;
      term next_tagged =
          `if cm_region_live (a0:cm_region)
           then cm_clear_tagged (tagged:int->bool) ${base:int} ${width:int}
           else tagged`;
      thm tail_tagged = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_restore_tagged_def(), not_boundary)), restored_tagged);
      gnode_list live_cases = BOOL_CASES_TAC(boundary_cases[1],
          `cm_region_live (a0:cm_region)`, "Hlive");
      {
        thm live = assume_rule(`cm_region_live (a0:cm_region)`);
        thm cleared_tagged = mp_rule(specl_rule(TERM_LIST(
            `a1:(cm_region)list`, `all:(cm_region)list`,
            `old:(cm_region)list`,
            `cm_clear_tagged (tagged:int->bool) ${base:int} ${width:int}`,
            `addr:int`), cm_restore_tagged_source),
            conv_rule(reduce_rewrite_conv(THM_LIST(live)), tail_tagged));
        thm cleared_open = conv_rule(reduce_rewrite_conv(THM_LIST(
            get_cm_clear_tagged_def())), cleared_tagged);
        thm safe_open = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_region_frame_safe_def, live)), head_safe);
        thm width_nonnegative = mp_rule(int_arith_rule(mk_imp(
            concl(conjunct1_rule(conjunct2_rule(safe_open))),
            `0i <= ${width:int}`)),
            conjunct1_rule(conjunct2_rule(safe_open)));
        thm no_interval = mp_rule(int_arith_rule(mk_imp(
            concl(conj_rule(width_nonnegative,
              conjunct2_rule(cleared_open))),
            `~(${base:int} <= (addr:int) &&
               addr < ${base:int} + ${width:int})`)),
            conj_rule(width_nonnegative, conjunct2_rule(cleared_open)));
        thm cleared_init_raw = conj_rule(old_init, no_interval);
        thm cleared_init = eq_mp_rule(sym_rule(apply_conversion(
            reduce_rewrite_conv(THM_LIST(get_cm_clear_init_def())),
            `cm_clear_init (init:int->bool) ${base:int} ${width:int}
              (addr:int)`)), cleared_init_raw);
        thm ih = specl_rule(TERM_LIST(
            `p:cm_program`, `all:(cm_region)list`, `fid:int`, `fp:int`,
            `old:(cm_region)list`,
            `cm_clear_init (init:int->bool) ${base:int} ${width:int}`,
            `cm_clear_tagged (tagged:int->bool) ${base:int} ${width:int}`,
            `addr:int`),
            assume_rule(goal_lasmps(live_cases[0]->g)[0].tm));
        ih = match_mp_rule(ih, tail_prefix);
        ih = match_mp_rule(ih,
            conv_rule(reduce_rewrite_conv(THM_LIST(live)), tail_tagged));
        ih = match_mp_rule(ih, cleared_init);
        thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
            get_cm_restore_init_def(), not_boundary, live)),
            goal_ccl(live_cases[0]->g));
        ACCEPT_TAC(live_cases[0], eq_mp_rule(sym_rule(target_view), ih));
      }
      {
        thm not_live = assume_rule(`~cm_region_live (a0:cm_region)`);
        thm ih = specl_rule(TERM_LIST(
            `p:cm_program`, `all:(cm_region)list`, `fid:int`, `fp:int`,
            `old:(cm_region)list`, `init:int->bool`, `tagged:int->bool`,
            `addr:int`),
            assume_rule(goal_lasmps(live_cases[1]->g)[0].tm));
        ih = match_mp_rule(ih, tail_prefix);
        ih = match_mp_rule(ih,
            conv_rule(reduce_rewrite_conv(THM_LIST(not_live)),
              tail_tagged));
        ih = match_mp_rule(ih, old_init);
        thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
            get_cm_restore_init_def(), not_boundary, not_live)),
            goal_ccl(live_cases[1]->g));
        ACCEPT_TAC(live_cases[1], eq_mp_rule(sym_rule(target_view), ih));
      }
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_restore_tagged_init_lockstep =
    cm_prove_restore_tagged_init_lockstep();

PROOF static thm cm_prove_restore_scope_live_source(void) {
  term active = `cm_state_regions (st:cm_src_state)`;
  term restored_regions =
      `cm_restore_regions ${active:(cm_region)list}
        (old:(cm_region)list)`;
  term restored =
      `cm_restore_scope (st:cm_src_state)
        (oldenv:int->int->cm_value) (old:(cm_region)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (oldenv:int->int->cm_value) (old:(cm_region)list)
         (addr:int).
         cm_region_prefix_safe p (cm_state_regions st) fid
           (cm_state_fp st) (cm_state_regions st) old ==>
         cm_live_address
           (cm_restore_scope st oldenv old) addr ==>
         cm_live_address st addr`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm prefix = assume_rule(
      `cm_region_prefix_safe (p:cm_program)
        ${active:(cm_region)list} (fid:int) (cm_state_fp st)
        ${active:(cm_region)list} (old:(cm_region)list)`);
  thm bases = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, active, `fid:int`, `cm_state_fp (st:cm_src_state)`,
      active, `old:(cm_region)list`), cm_restore_regions_bases), prefix);
  thm base_points = conv_rule(rewrite_conv(THM_LIST(
      cm_region_bases_equal_def)), bases);
  thm_list state_rules = get_cm_state_core_defs();
  vector_add(&state_rules, get_cm_restore_scope_def());
  thm new_live = conv_rule(then_conv(
      rewrite_conv(THM_LIST(cm_live_address_def)),
      reduce_rewrite_conv(state_rules)), assume_rule(
        `cm_live_address ${restored:cm_src_state} (addr:int)`));
  thm witness = assume_rule(
      `MEM (region:cm_region) ${restored_regions:(cm_region)list} &&
       cm_region_live region &&
       cm_region_base ${restored_regions:(cm_region)list}
           (cm_region_gen region) + cm_region_lo region <= (addr:int) &&
       addr < cm_region_base ${restored_regions:(cm_region)list}
           (cm_region_gen region) + cm_region_hi region`);
  thm member = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(active, `p:cm_program`, active,
        `fid:int`, `cm_state_fp (st:cm_src_state)`,
        `old:(cm_region)list`, `region:cm_region`),
        cm_restore_live_region_source), prefix), conjunct1_rule(witness)),
      conjunct1_rule(conjunct2_rule(witness)));
  thm base = spec_rule(`cm_region_gen (region:cm_region)`, base_points);
  thm bounds = conjunct2_rule(conjunct2_rule(witness));
  thm source_bounds = conj_rule(
      conv_rule(rewrite_conv(THM_LIST(base)), conjunct1_rule(bounds)),
      conv_rule(rewrite_conv(THM_LIST(base)), conjunct2_rule(bounds)));
  thm source_body = conj_rule(member, conj_rule(
      conjunct1_rule(conjunct2_rule(witness)), source_bounds));
  thm source_exists = exists_rule(
      `?candidate.
         MEM candidate ${active:(cm_region)list} &&
         cm_region_live candidate &&
         cm_region_base ${active:(cm_region)list}
             (cm_region_gen candidate) + cm_region_lo candidate <= (addr:int) &&
         addr < cm_region_base ${active:(cm_region)list}
             (cm_region_gen candidate) + cm_region_hi candidate`,
      `region:cm_region`, source_body);
  thm source_live = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_live_address_def)),
      `cm_live_address (st:cm_src_state) (addr:int)`)), source_exists);
  ACCEPT_TAC(leaf, choose_rule(`region:cm_region`, new_live, source_live));
  return gnode_prove(root);
}
PROOF static thm cm_restore_scope_live_source =
    cm_prove_restore_scope_live_source();

PROOF static thm cm_prove_restore_initialized_transport(void) {
  term restored =
      `cm_restore_scope (st:cm_src_state)
        (oldenv:int->int->cm_value) (old:(cm_region)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (oldenv:int->int->cm_value) (old:(cm_region)list)
         (mem:int->int).
         cm_region_prefix_safe p (cm_state_regions st) fid
           (cm_state_fp st) (cm_state_regions st) old ==>
         cm_initialized_bytes_sim st mem ==>
         cm_initialized_bytes_sim
           (cm_restore_scope st oldenv old) mem`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm prefix = assume_rule(
      `cm_region_prefix_safe (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int) (cm_state_fp st)
        (cm_state_regions st) (old:(cm_region)list)`);
  thm old_sim = conv_rule(rewrite_conv(THM_LIST(
      cm_initialized_bytes_sim_def)), assume_rule(
        `cm_initialized_bytes_sim (st:cm_src_state) (mem:int->int)`));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_initialized_bytes_sim_def)));
  gnode point = AUTO_INTROS_TAC(opened);
  thm new_parts = assume_rule(
      `cm_state_init ${restored:cm_src_state} (addr:int) &&
       cm_live_address ${restored:cm_src_state} (addr:int)`);
  thm_list state_rules = get_cm_state_core_defs();
  vector_add(&state_rules, get_cm_restore_scope_def());
  thm new_init = conv_rule(reduce_rewrite_conv(state_rules),
      conjunct1_rule(new_parts));
  thm old_init = mp_rule(specl_rule(TERM_LIST(
      `cm_state_regions (st:cm_src_state)`,
      `cm_state_regions (st:cm_src_state)`, `old:(cm_region)list`,
      `cm_state_init (st:cm_src_state)`, `addr:int`),
      cm_restore_init_source), new_init);
  thm old_live = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `oldenv:int->int->cm_value`, `old:(cm_region)list`, `addr:int`),
      cm_restore_scope_live_source), prefix);
  old_live = match_mp_rule(old_live, conjunct2_rule(new_parts));
  thm result = match_mp_rule(spec_rule(`addr:int`, old_sim),
      conj_rule(old_init, old_live));
  thm normalized = conv_rule(reduce_rewrite_conv(state_rules), result);
  thm target_view = apply_conversion(reduce_rewrite_conv(state_rules),
      goal_ccl(point->g));
  ACCEPT_TAC(point, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}
PROOF static thm cm_restore_initialized_transport =
    cm_prove_restore_initialized_transport();

PROOF static thm cm_prove_restore_provenance_transport(void) {
  term active = `cm_state_regions (st:cm_src_state)`;
  term restored =
      `cm_restore_scope (st:cm_src_state)
        (oldenv:int->int->cm_value) (old:(cm_region)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (oldenv:int->int->cm_value) (old:(cm_region)list)
         (mem:int->int).
         cm_region_prefix_safe p (cm_state_regions st) fid
           (cm_state_fp st) (cm_state_regions st) old ==>
         cm_state_tags_generation_below st (cm_state_nextgen st) ==>
         cm_stored_provenance_sim st mem ==>
         cm_stored_provenance_sim
           (cm_restore_scope st oldenv old) mem`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm prefix = assume_rule(
      `cm_region_prefix_safe (p:cm_program) ${active:(cm_region)list}
        (fid:int) (cm_state_fp st) ${active:(cm_region)list}
        (old:(cm_region)list)`);
  thm tag_below = assume_rule(
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`);
  thm old_sim = conv_rule(rewrite_conv(THM_LIST(
      cm_stored_provenance_sim_def)), assume_rule(
        `cm_stored_provenance_sim (st:cm_src_state) (mem:int->int)`));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_stored_provenance_sim_def)));
  gnode point = AUTO_INTROS_TAC(opened);
  thm new_parts = assume_rule(
      `cm_state_tagged ${restored:cm_src_state} (addr:int) &&
       cm_live_address ${restored:cm_src_state} (addr:int)`);
  thm_list state_rules = get_cm_state_core_defs();
  vector_add(&state_rules, get_cm_restore_scope_def());
  thm new_tagged = conv_rule(reduce_rewrite_conv(state_rules),
      conjunct1_rule(new_parts));
  thm old_tagged = mp_rule(specl_rule(TERM_LIST(active, active,
      `old:(cm_region)list`, `cm_state_tagged (st:cm_src_state)`,
      `addr:int`), cm_restore_tagged_source), new_tagged);
  thm old_live = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `oldenv:int->int->cm_value`, `old:(cm_region)list`, `addr:int`),
      cm_restore_scope_live_source), prefix);
  old_live = match_mp_rule(old_live, conjunct2_rule(new_parts));
  thm old_point = match_mp_rule(spec_rule(`addr:int`, old_sim),
      conj_rule(old_tagged, old_live));
  thm new_init = specl_rule(TERM_LIST(active, `p:cm_program`, active,
      `fid:int`, `cm_state_fp (st:cm_src_state)`, `old:(cm_region)list`,
      `cm_state_init (st:cm_src_state)`,
      `cm_state_tagged (st:cm_src_state)`, `addr:int`),
      cm_restore_tagged_init_lockstep);
  new_init = match_mp_rule(new_init, prefix);
  new_init = match_mp_rule(new_init, new_tagged);
  new_init = match_mp_rule(new_init, conjunct1_rule(old_point));
  thm bases = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, active, `fid:int`, `cm_state_fp (st:cm_src_state)`,
      active, `old:(cm_region)list`), cm_restore_regions_bases), prefix);
  thm below_bases = match_mp_rule(specl_rule(TERM_LIST(
      `cm_restore_regions ${active:(cm_region)list} (old:(cm_region)list)`,
      active, `cm_state_nextgen (st:cm_src_state)`),
      cm_region_bases_equal_below), bases);
  thm below_view = apply_conversion(reduce_rewrite_conv(state_rules),
      `cm_region_bases_below_equal
        (cm_state_regions ${restored:cm_src_state})
        (cm_state_regions (st:cm_src_state)) (cm_state_nextgen st)`);
  below_bases = eq_mp_rule(sym_rule(below_view), below_bases);
  thm below_open = conv_rule(rewrite_conv(THM_LIST(
      cm_state_tags_generation_below_def)), tag_below);
  thm value_below = match_mp_rule(spec_rule(`addr:int`, below_open),
      old_tagged);
  thm number = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_state_tags (st:cm_src_state) (addr:int)`,
      `st:cm_src_state`, restored, `cm_state_nextgen st`),
      cm_value_number_bases), below_bases), value_below);
  thm word = trans_rule(conjunct2_rule(old_point), sym_rule(number));
  thm result = conj_rule(new_init, word);
  thm normalized = conv_rule(reduce_rewrite_conv(state_rules), result);
  thm target_view = apply_conversion(reduce_rewrite_conv(state_rules),
      goal_ccl(point->g));
  ACCEPT_TAC(point, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}
PROOF static thm cm_restore_provenance_transport =
    cm_prove_restore_provenance_transport();

PROOF static thm cm_prove_machine_restore_scope(void) {
  term restored =
      `cm_restore_scope (st:cm_src_state)
        (oldenv:int->int->cm_value) (old:(cm_region)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (oldenv:int->int->cm_value) (old:(cm_region)list)
         (vm:tvm_state) (calls:(cm_call_sim_frame)list)
         (spills:(cm_spill_frame)list) (values:(cm_value)list).
         cm_region_prefix_safe p (cm_state_regions st) fid
           (cm_state_fp st) (cm_state_regions st) old ==>
         cm_state_tags_generation_below st (cm_state_nextgen st) ==>
         cm_spill_frames_generation_below
           (cm_state_nextgen st) spills ==>
         cm_values_generation_below (cm_state_nextgen st) values ==>
         cm_machine_state_sim p st vm calls spills values [] ==>
         cm_machine_state_sim p
           (cm_restore_scope st oldenv old) vm calls spills values []`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm prefix = assume_rule(
      `cm_region_prefix_safe (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int) (cm_state_fp st)
        (cm_state_regions st) (old:(cm_region)list)`);
  thm tag_below = assume_rule(
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`);
  thm spill_below = assume_rule(
      `cm_spill_frames_generation_below (cm_state_nextgen st)
        (spills:(cm_spill_frame)list)`);
  thm values_below = assume_rule(
      `cm_values_generation_below (cm_state_nextgen st)
        (values:(cm_value)list)`);
  thm old_sim = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
        (vm:tvm_state) (calls:(cm_call_sim_frame)list)
        (spills:(cm_spill_frame)list) (values:(cm_value)list) []`);
  thm parts = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_machine_state_sim_def)), concl(old_sim)),
      old_sim);
  thm initialized = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `oldenv:int->int->cm_value`, `old:(cm_region)list`,
      `tvm_mem (vm:tvm_state)`), cm_restore_initialized_transport),
      prefix), conjunct1_rule(parts));
  parts = conjunct2_rule(parts);
  thm provenance = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(`p:cm_program`, `fid:int`, `st:cm_src_state`,
        `oldenv:int->int->cm_value`, `old:(cm_region)list`,
        `tvm_mem (vm:tvm_state)`), cm_restore_provenance_transport),
      prefix), tag_below), conjunct1_rule(parts));
  parts = conjunct2_rule(parts);
  thm frame_pointer = conjunct1_rule(parts);
  parts = conjunct2_rule(parts);
  thm calls_sim = conjunct1_rule(parts);
  parts = conjunct2_rule(parts);
  thm old_spills = conjunct1_rule(parts);
  parts = conjunct2_rule(parts);
  thm input = conjunct1_rule(parts);
  parts = conjunct2_rule(parts);
  thm output = conjunct1_rule(parts);
  thm operands = conjunct2_rule(parts);
  thm bases = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `cm_state_regions (st:cm_src_state)`, `fid:int`,
      `cm_state_fp (st:cm_src_state)`, `cm_state_regions st`,
      `old:(cm_region)list`), cm_restore_regions_bases), prefix);
  thm below_bases = match_mp_rule(specl_rule(TERM_LIST(
      `cm_restore_regions (cm_state_regions (st:cm_src_state))
        (old:(cm_region)list)`,
      `cm_state_regions (st:cm_src_state)`,
      `cm_state_nextgen (st:cm_src_state)`),
      cm_region_bases_equal_below), bases);
  thm_list state_rules = get_cm_state_core_defs();
  vector_add(&state_rules, get_cm_restore_scope_def());
  thm below_view = apply_conversion(reduce_rewrite_conv(state_rules),
      `cm_region_bases_below_equal
        (cm_state_regions ${restored:cm_src_state})
        (cm_state_regions (st:cm_src_state)) (cm_state_nextgen st)`);
  below_bases = eq_mp_rule(sym_rule(below_view), below_bases);
  thm new_spills = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(`spills:(cm_spill_frame)list`,
        `p:cm_program`, `st:cm_src_state`, restored,
        `tvm_mem (vm:tvm_state)`, `cm_state_nextgen st`),
        cm_spill_frames_sim_bases), below_bases), spill_below), old_spills);
  thm new_operands = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(`st:cm_src_state`, restored,
        `values:(cm_value)list`, `[]:(int)list`,
        `tvm_stack (vm:tvm_state)`, `cm_state_nextgen st`),
        cm_operand_suffix_sim_bases), below_bases), values_below), operands);
  thm fp_equal = apply_conversion(reduce_rewrite_conv(state_rules),
      `cm_state_fp ${restored:cm_src_state}`);
  thm input_equal = apply_conversion(reduce_rewrite_conv(state_rules),
      `cm_state_input ${restored:cm_src_state}`);
  thm output_equal = apply_conversion(reduce_rewrite_conv(state_rules),
      `cm_state_output ${restored:cm_src_state}`);
  frame_pointer = trans_rule(frame_pointer, sym_rule(fp_equal));
  input = trans_rule(input, sym_rule(input_equal));
  output = trans_rule(output, sym_rule(output_equal));
  thm rebuilt = conj_rule(initialized, conj_rule(provenance,
      conj_rule(frame_pointer, conj_rule(calls_sim,
        conj_rule(new_spills, conj_rule(input,
          conj_rule(output, new_operands)))))));
  thm target_view = apply_conversion(
      rewrite_conv(THM_LIST(cm_machine_state_sim_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), rebuilt));
  return gnode_prove(root);
}
PROOF static thm cm_machine_restore_scope =
    cm_prove_machine_restore_scope();

PROOF static thm cm_prove_target_restore_scope_same(void) {
  term restored =
      `cm_restore_scope (st:cm_src_state)
        (oldenv:int->int->cm_value) (old:(cm_region)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (oldenv:int->int->cm_value) (old:(cm_region)list)
         (ann:cm_annotation) (target:tvm_task)
         (values:(cm_value)list).
         cm_region_prefix_safe p (cm_state_regions st) fid
           (cm_state_fp st) (cm_state_regions st) old ==>
         cm_state_tags_generation_below st (cm_state_nextgen st) ==>
         cm_spill_frames_generation_below (cm_state_nextgen st)
           (cm_active_spill_frames fid st ann) ==>
         cm_values_generation_below (cm_state_nextgen st) values ==>
         cm_running_target_sim p fid st values ann target ==>
         cm_running_target_sim p fid
           (cm_restore_scope st oldenv old) values ann target`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state) (values:(cm_value)list)
        (ann:cm_annotation) (target:tvm_task)`);
  thm expanded = conv_rule(rewrite_conv(THM_LIST(
      cm_running_target_sim_def)), old_running);
  thm body = assume_rule(
      `(target:tvm_task) == TVMRunTask (cm_compile_model (p:cm_program))
          (vm:tvm_state) &&
       tvm_pc vm == cm_ann_pc (ann:cm_annotation) &&
       cm_machine_state_sim p (st:cm_src_state) vm
         (cm_ann_calls ann) (cm_active_spill_frames (fid:int) st ann)
         (values:(cm_value)list) []`);
  thm machine = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `oldenv:int->int->cm_value`, `old:(cm_region)list`,
      `vm:tvm_state`, `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `values:(cm_value)list`), cm_machine_restore_scope);
  machine = match_mp_rule(machine, assume_rule(
      `cm_region_prefix_safe (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int) (cm_state_fp st)
        (cm_state_regions st) (old:(cm_region)list)`));
  machine = match_mp_rule(machine, assume_rule(
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`));
  machine = match_mp_rule(machine, assume_rule(
      `cm_spill_frames_generation_below (cm_state_nextgen st)
        (cm_active_spill_frames (fid:int) st (ann:cm_annotation))`));
  machine = match_mp_rule(machine, assume_rule(
      `cm_values_generation_below (cm_state_nextgen st)
        (values:(cm_value)list)`));
  machine = match_mp_rule(machine,
      conjunct2_rule(conjunct2_rule(body)));
  thm_list state_rules = get_cm_state_core_defs();
  vector_add(&state_rules, get_cm_restore_scope_def());
  vector_add(&state_rules, cm_active_spill_frames_def);
  thm old_active = apply_conversion(reduce_rewrite_conv(state_rules),
      `cm_active_spill_frames (fid:int) (st:cm_src_state)
        (ann:cm_annotation)`);
  thm new_active = apply_conversion(reduce_rewrite_conv(state_rules),
      `cm_active_spill_frames (fid:int) ${restored:cm_src_state}
        (ann:cm_annotation)`);
  thm active_equal = trans_rule(old_active, sym_rule(new_active));
  machine = eq_mp_rule(beta_norm(ap_term_rule(
      `\frames:(cm_spill_frame)list.
         cm_machine_state_sim (p:cm_program) ${restored:cm_src_state}
           (vm:tvm_state) (cm_ann_calls (ann:cm_annotation))
           frames (values:(cm_value)list) []`, active_equal)), machine);
  term exists_body =
      `?next_vm.
         (target:tvm_task) == TVMRunTask (cm_compile_model (p:cm_program))
           (next_vm:tvm_state) &&
         tvm_pc next_vm == cm_ann_pc (ann:cm_annotation) &&
         cm_machine_state_sim p ${restored:cm_src_state} next_vm
           (cm_ann_calls ann)
           (cm_active_spill_frames (fid:int) ${restored:cm_src_state} ann)
           (values:(cm_value)list) []`;
  thm witness = exists_rule(exists_body, `vm:tvm_state`,
      conj_rule(conjunct1_rule(body),
        conj_rule(conjunct1_rule(conjunct2_rule(body)), machine)));
  thm chosen = choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_running_target_sim_def)));
  ACCEPT_TAC(opened, chosen);
  return gnode_prove(root);
}
PROOF static thm cm_target_restore_scope_same =
    cm_prove_target_restore_scope_same();

PROOF static thm cm_prove_target_restore_scope(void) {
  term restored =
      `cm_restore_scope (st:cm_src_state)
        (oldenv:int->int->cm_value) (old:(cm_region)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (oldenv:int->int->cm_value) (old:(cm_region)list)
         (ann:cm_annotation) (ann2:cm_annotation) (target:tvm_task)
         (values:(cm_value)list).
         cm_region_prefix_safe p (cm_state_regions st) fid
           (cm_state_fp st) (cm_state_regions st) old ==>
         cm_state_tags_generation_below st (cm_state_nextgen st) ==>
         cm_spill_frames_generation_below (cm_state_nextgen st)
           (cm_active_spill_frames fid st ann) ==>
         cm_values_generation_below (cm_state_nextgen st) values ==>
         cm_ann_pc ann2 == cm_ann_pc ann ==>
         cm_ann_calls ann2 == cm_ann_calls ann ==>
         cm_ann_spills ann2 == cm_ann_spills ann ==>
         cm_ann_saved ann2 == cm_ann_saved ann ==>
         cm_running_target_sim p fid st values ann target ==>
         cm_running_target_sim p fid
           (cm_restore_scope st oldenv old) values ann2 target`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm restored_same = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `oldenv:int->int->cm_value`, `old:(cm_region)list`,
      `ann:cm_annotation`, `target:tvm_task`, `values:(cm_value)list`),
      cm_target_restore_scope_same);
  for (size_t i = 0; i < 5; ++i) {
    restored_same = match_mp_rule(restored_same,
        assume_rule(dest_imp(concl(restored_same)).tm1));
  }
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, restored, `values:(cm_value)list`,
      `ann:cm_annotation`, `ann2:cm_annotation`, `target:tvm_task`),
      cm_target_reannotate);
  for (size_t i = 0; i < 4; ++i) {
    reannotated = match_mp_rule(reannotated,
        assume_rule(dest_imp(concl(reannotated)).tm1));
  }
  reannotated = match_mp_rule(reannotated, restored_same);
  ACCEPT_TAC(leaf, reannotated);
  return gnode_prove(root);
}
PROOF thm cm_target_restore_scope =
    cm_prove_target_restore_scope();

PROOF thm get_cm_target_restore_scope(void) {
  return cm_target_restore_scope;
}

PROOF static thm cm_prove_target_restore_scope_halted_same(void) {
  term restored =
      `cm_restore_scope (st:cm_src_state)
        (oldenv:int->int->cm_value) (old:(cm_region)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (oldenv:int->int->cm_value) (old:(cm_region)list)
         (ann:cm_annotation) (target:tvm_task) (status:int).
         cm_region_prefix_safe p (cm_state_regions st) fid
           (cm_state_fp st) (cm_state_regions st) old ==>
         cm_state_tags_generation_below st (cm_state_nextgen st) ==>
         cm_spill_frames_generation_below (cm_state_nextgen st)
           (cm_active_spill_frames fid st ann) ==>
         cm_halted_target_sim p fid st status T ann target ==>
         cm_halted_target_sim p fid
           (cm_restore_scope st oldenv old) status T ann target`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_halted = assume_rule(
      `cm_halted_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state) (status:int) T
        (ann:cm_annotation) (target:tvm_task)`);
  thm expanded = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_halted_target_sim_def, cm_active_spill_frames_def)), old_halted);
  thm body = assume_rule(
      `(target:tvm_task) ==
          TVMDoneTask (vm:tvm_state) (status:int) 0i &&
       tvm_pc vm == cm_ann_pc (ann:cm_annotation) &&
       cm_machine_state_sim p (st:cm_src_state) vm
         (cm_ann_calls ann)
         (CMSpillFrame (fid:int) (cm_state_fp st)
            (cm_ann_spills ann) :: cm_ann_saved ann)
         [] []`);
  thm empty_below = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_values_generation_below_def)),
      `cm_values_generation_below (cm_state_nextgen st)
        ([]:(cm_value)list)`));
  thm machine = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `oldenv:int->int->cm_value`, `old:(cm_region)list`,
      `vm:tvm_state`, `cm_ann_calls (ann:cm_annotation)`,
      `CMSpillFrame (fid:int) (cm_state_fp st)
        (cm_ann_spills ann) :: cm_ann_saved ann`,
      `[]:(cm_value)list`), cm_machine_restore_scope);
  machine = match_mp_rule(machine, assume_rule(
      `cm_region_prefix_safe (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int) (cm_state_fp st)
        (cm_state_regions st) (old:(cm_region)list)`));
  machine = match_mp_rule(machine, assume_rule(
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`));
  machine = match_mp_rule(machine, conv_rule(rewrite_conv(THM_LIST(
      cm_active_spill_frames_def)), assume_rule(
        `cm_spill_frames_generation_below (cm_state_nextgen st)
          (cm_active_spill_frames (fid:int) st (ann:cm_annotation))`)));
  machine = match_mp_rule(machine, empty_below);
  machine = match_mp_rule(machine,
      conjunct2_rule(conjunct2_rule(body)));
  thm_list state_rules = get_cm_state_core_defs();
  vector_add(&state_rules, get_cm_restore_scope_def());
  thm fp_equal = apply_conversion(reduce_rewrite_conv(state_rules),
      `cm_state_fp ${restored:cm_src_state}`);
  thm active_equal = beta_norm(ap_term_rule(
      `\restored_fp:int.
         CMSpillFrame (fid:int) restored_fp
           (cm_ann_spills (ann:cm_annotation)) :: cm_ann_saved ann`,
      sym_rule(fp_equal)));
  machine = eq_mp_rule(beta_norm(ap_term_rule(
      `\frames:(cm_spill_frame)list.
         cm_machine_state_sim (p:cm_program) ${restored:cm_src_state}
           (vm:tvm_state) (cm_ann_calls (ann:cm_annotation))
           frames [] []`, active_equal)), machine);
  term exists_body =
      `?next_vm.
         (target:tvm_task) ==
           TVMDoneTask (next_vm:tvm_state) (status:int) 0i &&
         tvm_pc next_vm == cm_ann_pc (ann:cm_annotation) &&
         cm_machine_state_sim p ${restored:cm_src_state} next_vm
           (cm_ann_calls ann)
           (CMSpillFrame (fid:int) (cm_state_fp ${restored:cm_src_state})
              (cm_ann_spills ann) :: cm_ann_saved ann)
           [] []`;
  thm witness = exists_rule(exists_body, `vm:tvm_state`,
      conj_rule(conjunct1_rule(body),
        conj_rule(conjunct1_rule(conjunct2_rule(body)), machine)));
  thm chosen = choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_halted_target_sim_def, cm_active_spill_frames_def)));
  ACCEPT_TAC(opened, chosen);
  return gnode_prove(root);
}
PROOF static thm cm_target_restore_scope_halted_same =
    cm_prove_target_restore_scope_halted_same();

PROOF static thm cm_prove_target_restore_scope_halted(void) {
  term restored =
      `cm_restore_scope (st:cm_src_state)
        (oldenv:int->int->cm_value) (old:(cm_region)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (oldenv:int->int->cm_value) (old:(cm_region)list)
         (ann:cm_annotation) (ann2:cm_annotation)
         (target:tvm_task) (status:int).
         cm_region_prefix_safe p (cm_state_regions st) fid
           (cm_state_fp st) (cm_state_regions st) old ==>
         cm_state_tags_generation_below st (cm_state_nextgen st) ==>
         cm_spill_frames_generation_below (cm_state_nextgen st)
           (cm_active_spill_frames fid st ann) ==>
         cm_ann_pc ann2 == cm_ann_pc ann ==>
         cm_ann_calls ann2 == cm_ann_calls ann ==>
         cm_ann_spills ann2 == cm_ann_spills ann ==>
         cm_ann_saved ann2 == cm_ann_saved ann ==>
         cm_halted_target_sim p fid st status T ann target ==>
         cm_halted_target_sim p fid
           (cm_restore_scope st oldenv old) status T ann2 target`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm restored_same = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `oldenv:int->int->cm_value`, `old:(cm_region)list`,
      `ann:cm_annotation`, `target:tvm_task`, `status:int`),
      cm_target_restore_scope_halted_same);
  for (size_t i = 0; i < 4; ++i) {
    restored_same = match_mp_rule(restored_same,
        assume_rule(dest_imp(concl(restored_same)).tm1));
  }
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, restored, `status:int`, `T:bool`,
      `ann:cm_annotation`, `ann2:cm_annotation`, `target:tvm_task`),
      cm_target_halted_reannotate);
  for (size_t i = 0; i < 4; ++i) {
    reannotated = match_mp_rule(reannotated,
        assume_rule(dest_imp(concl(reannotated)).tm1));
  }
  reannotated = match_mp_rule(reannotated, restored_same);
  ACCEPT_TAC(leaf, reannotated);
  return gnode_prove(root);
}
PROOF thm cm_target_restore_scope_halted =
    cm_prove_target_restore_scope_halted();

PROOF thm get_cm_target_restore_scope_halted(void) {
  return cm_target_restore_scope_halted;
}
PROOF thm get_cm_region_bases_equal_below(void) {
  return cm_region_bases_equal_below;
}

PROOF thm get_cm_restore_initialized_transport(void) {
  return cm_restore_initialized_transport;
}

PROOF thm get_cm_restore_provenance_transport(void) {
  return cm_restore_provenance_transport;
}
PROOF thm get_cm_restore_tagged_init_lockstep(void) {
  return cm_restore_tagged_init_lockstep;
}

PROOF thm get_cm_restore_scope_live_source(void) {
  return cm_restore_scope_live_source;
}



PROOF static int cmc_preservation_target_restore_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_restore_axioms_before,
      "cmc_preservation_target_restore introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_restore_scope)) == 0 &&
      vector_size(hyp(cm_target_restore_scope_halted)) == 0,
      "scope target transport theorem has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_restore_checks =
    cmc_preservation_target_restore_final_checks();
