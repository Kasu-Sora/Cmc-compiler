#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_tagged_restore.h"
#include "cmc_preservation_invariant_step.h"

#require "cmc_preservation_tagged_restore_list.c"

PROOF static size_t _cmc_preservation_tagged_restore_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_tagged_span_restore_core(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (frame_fp:int)
         (st:cm_src_state) (old:(cm_region)list)
         (env:int->int->cm_value) (newfp:int).
         cm_region_prefix_safe p (cm_state_regions st)
           fid frame_fp (cm_state_regions st) old ==>
         cm_tagged_span_valid st ==>
         cm_tagged_span_valid
           (cm_state_make (cm_state_mem st)
             (cm_restore_init (cm_state_regions st)
               (cm_state_regions st) old (cm_state_init st))
             (cm_state_tags st)
             (cm_restore_tagged (cm_state_regions st)
               (cm_state_regions st) old (cm_state_tagged st))
             env (cm_state_input st) (cm_state_output st) newfp
             (cm_state_nextgen st)
             (cm_restore_regions (cm_state_regions st) old))`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  term active = `cm_state_regions (st:cm_src_state)`;
  term restored_regions =
      `cm_restore_regions ${active:(cm_region)list}
        (old:(cm_region)list)`;
  term restored_tagged =
      `cm_restore_tagged ${active:(cm_region)list}
        ${active:(cm_region)list} (old:(cm_region)list)
        (cm_state_tagged (st:cm_src_state))`;
  term restored_state =
      `cm_state_make (cm_state_mem (st:cm_src_state))
        (cm_restore_init ${active:(cm_region)list}
          ${active:(cm_region)list} (old:(cm_region)list)
          (cm_state_init st))
        (cm_state_tags st) ${restored_tagged:int->bool}
        (env:int->int->cm_value) (cm_state_input st)
        (cm_state_output st) (newfp:int) (cm_state_nextgen st)
        ${restored_regions:(cm_region)list}`;
  thm prefix = assume_rule(
      `cm_region_prefix_safe (p:cm_program)
        ${active:(cm_region)list} (fid:int) (frame_fp:int)
        ${active:(cm_region)list} (old:(cm_region)list)`);
  thm old_valid = conv_rule(rewrite_conv(THM_LIST(
      cm_tagged_span_valid_def)), assume_rule(
        `cm_tagged_span_valid (st:cm_src_state)`));
  thm bases = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, active, `fid:int`, `frame_fp:int`, active,
      `old:(cm_region)list`), cm_restore_regions_bases), prefix);
  thm base_points = conv_rule(rewrite_conv(THM_LIST(
      cm_region_bases_equal_def)), bases);

  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_tagged_span_valid_def)));
  gnode at_address = AUTO_INTROS_TAC(opened);
  thm new_parts = assume_rule(
      `cm_state_tagged ${restored_state:cm_src_state} (addr:int) &&
       cm_live_address ${restored_state:cm_src_state} (addr:int)`);
  thm_list state_rules = get_cm_state_core_defs();
  thm new_tagged = conv_rule(reduce_rewrite_conv(state_rules),
      conjunct1_rule(new_parts));
  thm new_live = conv_rule(then_conv(
      rewrite_conv(THM_LIST(cm_live_address_def)),
      reduce_rewrite_conv(state_rules)),
      conjunct2_rule(new_parts));
  thm old_tagged = mp_rule(specl_rule(TERM_LIST(
      active, active, `old:(cm_region)list`,
      `cm_state_tagged (st:cm_src_state)`, `addr:int`),
      cm_restore_tagged_source), new_tagged);

  thm live_witness = assume_rule(
      `MEM (region:cm_region) ${restored_regions:(cm_region)list} &&
       cm_region_live region &&
       cm_region_base ${restored_regions:(cm_region)list}
           (cm_region_gen region) + cm_region_lo region <= (addr:int) &&
       addr < cm_region_base ${restored_regions:(cm_region)list}
           (cm_region_gen region) + cm_region_hi region`);
  thm restored_member = conjunct1_rule(live_witness);
  thm witness_live = conjunct1_rule(conjunct2_rule(live_witness));
  thm restored_bounds = conjunct2_rule(conjunct2_rule(live_witness));
  thm source_member = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        active, `p:cm_program`, active, `fid:int`, `frame_fp:int`,
        `old:(cm_region)list`, `region:cm_region`),
        cm_restore_live_region_source), prefix), restored_member),
      witness_live);
  thm base_at_witness = spec_rule(
      `cm_region_gen (region:cm_region)`, base_points);
  thm source_lower = conv_rule(rewrite_conv(THM_LIST(
      base_at_witness)), conjunct1_rule(restored_bounds));
  thm source_upper = conv_rule(rewrite_conv(THM_LIST(
      base_at_witness)), conjunct2_rule(restored_bounds));
  thm source_bounds = conj_rule(source_lower, source_upper);
  thm source_body = conj_rule(source_member,
      conj_rule(witness_live, source_bounds));
  thm source_exists = exists_rule(
      `?candidate.
         MEM candidate ${active:(cm_region)list} &&
         cm_region_live candidate &&
         cm_region_base ${active:(cm_region)list}
             (cm_region_gen candidate) +
             cm_region_lo candidate <= (addr:int) &&
         addr < cm_region_base ${active:(cm_region)list}
             (cm_region_gen candidate) + cm_region_hi candidate`,
      `region:cm_region`, source_body);
  thm source_live = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_live_address_def)),
      `cm_live_address (st:cm_src_state) (addr:int)`)),
      source_exists);
  thm old_span = match_mp_rule(spec_rule(`addr:int`, old_valid),
      conj_rule(old_tagged, source_live));
  thm old_span_open = conv_rule(rewrite_conv(THM_LIST(
      cm_live_span_def)), old_span);

  term byte_interval =
      `(addr:int) <= (byte:int) && byte < addr + 8i`;
  thm old_byte_live = mp_rule(spec_rule(`byte:int`, old_span_open),
      assume_rule(byte_interval));
  thm old_byte_exists = conv_rule(rewrite_conv(THM_LIST(
      cm_live_address_def)), old_byte_live);
  thm byte_witness = assume_rule(
      `MEM (byte_region:cm_region) ${active:(cm_region)list} &&
       cm_region_live byte_region &&
       cm_region_base ${active:(cm_region)list}
           (cm_region_gen byte_region) +
           cm_region_lo byte_region <= (byte:int) &&
       byte < cm_region_base ${active:(cm_region)list}
           (cm_region_gen byte_region) + cm_region_hi byte_region`);
  thm kept = specl_rule(TERM_LIST(
      active, active, `old:(cm_region)list`,
      `cm_state_tagged (st:cm_src_state)`, `addr:int`, `byte:int`,
      `byte_region:cm_region`), cm_restore_tagged_keeps_region);
  kept = match_mp_rule(kept, conjunct1_rule(byte_witness));
  kept = match_mp_rule(kept,
      conjunct1_rule(conjunct2_rule(byte_witness)));
  kept = match_mp_rule(kept,
      conjunct2_rule(conjunct2_rule(byte_witness)));
  kept = match_mp_rule(kept, assume_rule(byte_interval));
  kept = match_mp_rule(kept, new_tagged);
  thm byte_base = spec_rule(
      `cm_region_gen (byte_region:cm_region)`, base_points);
  thm byte_source_bounds =
      conjunct2_rule(conjunct2_rule(byte_witness));
  thm byte_restored_lower = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(byte_base))), conjunct1_rule(byte_source_bounds));
  thm byte_restored_upper = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(byte_base))), conjunct2_rule(byte_source_bounds));
  thm byte_restored_bounds = conj_rule(
      byte_restored_lower, byte_restored_upper);
  thm restored_byte_body = conj_rule(conjunct1_rule(kept),
      conj_rule(conjunct2_rule(kept), byte_restored_bounds));
  thm restored_byte_exists = exists_rule(
      `?candidate.
         MEM candidate ${restored_regions:(cm_region)list} &&
         cm_region_live candidate &&
         cm_region_base ${restored_regions:(cm_region)list}
             (cm_region_gen candidate) +
             cm_region_lo candidate <= (byte:int) &&
         byte < cm_region_base ${restored_regions:(cm_region)list}
             (cm_region_gen candidate) + cm_region_hi candidate`,
      `byte_region:cm_region`, restored_byte_body);
  thm restored_live_view = apply_conversion(then_conv(
      rewrite_conv(THM_LIST(cm_live_address_def)),
      reduce_rewrite_conv(state_rules)),
      `cm_live_address ${restored_state:cm_src_state} (byte:int)`);
  thm restored_byte_live = eq_mp_rule(
      sym_rule(restored_live_view), restored_byte_exists);
  thm byte_result = choose_rule(`byte_region:cm_region`,
      old_byte_exists, restored_byte_live);
  thm restored_span_open = gen_rule(`byte:int`,
      disch_rule(byte_interval, byte_result));
  thm restored_span = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_live_span_def)),
      `cm_live_span ${restored_state:cm_src_state} (addr:int) 8i`)),
      restored_span_open);
  thm address_result = choose_rule(`region:cm_region`,
      new_live, restored_span);
  ACCEPT_TAC(at_address, address_result);
  return gnode_prove(root_node);
}
PROOF static thm cm_tagged_span_restore_core =
    cm_prove_tagged_span_restore_core();

PROOF static thm cm_prove_tagged_span_restore_scope(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (fp:int) (st:cm_src_state)
         (oldenv:int->int->cm_value) (old:(cm_region)list).
         cm_region_prefix_safe p (cm_state_regions st)
           fid fp (cm_state_regions st) old ==>
         cm_tagged_span_valid st ==>
         cm_tagged_span_valid (cm_restore_scope st oldenv old)`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  thm core = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `fp:int`, `st:cm_src_state`,
      `old:(cm_region)list`, `oldenv:int->int->cm_value`,
      `cm_state_fp (st:cm_src_state)`),
      cm_tagged_span_restore_core);
  core = match_mp_rule(core, assume_rule(
      `cm_region_prefix_safe (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int) (fp:int)
        (cm_state_regions st) (old:(cm_region)list)`));
  core = match_mp_rule(core, assume_rule(
      `cm_tagged_span_valid (st:cm_src_state)`));
  thm target_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_restore_scope_def())), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), core));
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_restore_scope =
    cm_prove_tagged_span_restore_scope();

PROOF static thm cm_prove_tagged_span_restore_call(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (fp:int) (st:cm_src_state)
         (oldenv:int->int->cm_value) (oldfp:int)
         (old:(cm_region)list).
         cm_region_prefix_safe p (cm_state_regions st)
           fid fp (cm_state_regions st) old ==>
         cm_tagged_span_valid st ==>
         cm_tagged_span_valid
           (cm_restore_call st oldenv oldfp old)`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  thm core = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `fp:int`, `st:cm_src_state`,
      `old:(cm_region)list`, `oldenv:int->int->cm_value`,
      `oldfp:int`), cm_tagged_span_restore_core);
  core = match_mp_rule(core, assume_rule(
      `cm_region_prefix_safe (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int) (fp:int)
        (cm_state_regions st) (old:(cm_region)list)`));
  core = match_mp_rule(core, assume_rule(
      `cm_tagged_span_valid (st:cm_src_state)`));
  thm target_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_restore_call_def())), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), core));
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_restore_call =
    cm_prove_tagged_span_restore_call();

PROOF static int cmc_preservation_tagged_restore_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_tagged_restore_axioms_before,
      "cmc_preservation_tagged_restore introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_restore_scope)) == 0,
      "restore-scope tagged-span theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_restore_call)) == 0,
      "restore-call tagged-span theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_tagged_restore_checks =
    cmc_preservation_tagged_restore_final_checks();
