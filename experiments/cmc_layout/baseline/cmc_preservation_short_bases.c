#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_short_bases.h"
#include "cmc_preservation_invariant_transition.h"

#require "cmc_preservation_invariant_transition.c"

PROOF static size_t _cmc_preservation_short_bases_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_region_bases_equal_below_short(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:(cm_region)list) (right:(cm_region)list)
         (limit:int).
         cm_region_bases_equal left right ==>
         cm_region_bases_below_equal left right limit`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm equal = conv_rule(rewrite_conv(THM_LIST(
      cm_region_bases_equal_def)), assume_rule(
        `cm_region_bases_equal (left:(cm_region)list)
          (right:(cm_region)list)`));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_region_bases_below_equal_def)));
  gnode with_gen = GEN_TAC(opened, "gen");
  gnode with_bound = DISCH_TAC(with_gen, "Hgen_bound");
  ACCEPT_TAC(with_bound, spec_rule(`gen:int`, equal));
  return gnode_prove(root);
}
PROOF static thm cm_region_bases_equal_below_short =
    cm_prove_region_bases_equal_below_short();

PROOF static thm cm_prove_activate_local_region_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (slot:int) (st:cm_src_state).
         cm_region_bases_below_equal
           (cm_state_regions (cm_activate_local p fid slot st))
           (cm_state_regions st) (cm_state_nextgen st)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term fresh = `CMRegion (cm_state_nextgen (st:cm_src_state))
      (cm_local_base (p:cm_program) (fid:int) (slot:int)
        (cm_state_fp st)) 0i
      (cm_slot_size (cm_program_structs p)
        (inth slot (cm_function_locals
          (inth fid (cm_program_functions p))))) T T`;
  thm fresh_rule = specl_rule(TERM_LIST(
      fresh, `cm_state_regions (st:cm_src_state)`,
      `cm_state_nextgen (st:cm_src_state)`),
      cm_region_bases_fresh_cons);
  term needed = dest_imp(concl(fresh_rule)).tm1;
  thm needed_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_region_gen_def())), needed);
  thm reflexive = ispec_rule(
      `cm_state_nextgen (st:cm_src_state)`,
      int_arith_rule(`!(x:int). x <= x`));
  thm fresh_bases = match_mp_rule(fresh_rule,
      eq_mp_rule(sym_rule(needed_view), reflexive));
  thm_list state_rules = get_cm_state_core_defs();
  thm target_view = apply_conversion(then_conv(
      rewrite_conv(THM_LIST(get_cm_activate_local_def())),
      reduce_rewrite_conv(state_rules)),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), fresh_bases));
  return gnode_prove(root);
}
PROOF thm cm_activate_local_region_bases =
    cm_prove_activate_local_region_bases();

PROOF static thm cm_prove_runtime_scope_restore_region_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ann:cm_annotation) (phase:cm_aphase)
         (oldenv:int->int->cm_value)
         (oldregions:(cm_region)list)
         (owner:int) (owner_break:int) (owner_continue:int)
         (rest:(cm_acursor)list).
         cm_ann_cursors ann ==
           CMACursor phase owner owner_break owner_continue :: rest ==>
         cm_phase_is_scope phase ==>
         ~cm_phase_is_call phase ==>
         cm_phase_oldregions phase == oldregions ==>
         cm_runtime_core p fid st ann ==>
         cm_region_bases_below_equal
           (cm_state_regions (cm_restore_scope st oldenv oldregions))
           (cm_state_regions st) (cm_state_nextgen st)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm cursor_eq = assume_rule(
      `cm_ann_cursors (ann:cm_annotation) ==
       CMACursor (phase:cm_aphase) (owner:int)
         (owner_break:int) (owner_continue:int) ::
       (rest:(cm_acursor)list)`);
  thm scope = assume_rule(`cm_phase_is_scope (phase:cm_aphase)`);
  thm not_call = assume_rule(`~cm_phase_is_call (phase:cm_aphase)`);
  thm oldregions_eq = assume_rule(
      `cm_phase_oldregions (phase:cm_aphase) ==
       (oldregions:(cm_region)list)`);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      cm_runtime_core_def)), assume_rule(
        `cm_runtime_core (p:cm_program) (fid:int)
          (st:cm_src_state) (ann:cm_annotation)`));
  thm shaped_stack = conv_rule(rewrite_conv(THM_LIST(cursor_eq)),
      conjunct2_rule(opened));
  thm stack_body = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_runtime_stack_def, cm_cursor_phase_def,
      not_call, scope, oldregions_eq)), shaped_stack);
  thm prefix = conjunct1_rule(conjunct2_rule(stack_body));
  thm full = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
      `fid:int`, `cm_state_fp (st:cm_src_state)`,
      `cm_state_regions (st:cm_src_state)`,
      `oldregions:(cm_region)list`), cm_restore_regions_bases),
      prefix);
  thm below = match_mp_rule(specl_rule(TERM_LIST(
      `cm_restore_regions (cm_state_regions (st:cm_src_state))
        (oldregions:(cm_region)list)`,
      `cm_state_regions (st:cm_src_state)`,
      `cm_state_nextgen (st:cm_src_state)`),
      cm_region_bases_equal_below_short), full);
  thm structure = specl_rule(TERM_LIST(
      `st:cm_src_state`, `oldenv:int->int->cm_value`,
      `oldregions:(cm_region)list`), cm_restore_scope_structure);
  thm regions_structure =
      conjunct2_rule(conjunct2_rule(structure));
  thm target_view = apply_conversion(rewrite_conv(THM_LIST(
      regions_structure)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), below));
  return gnode_prove(root);
}
PROOF thm cm_runtime_scope_restore_region_bases =
    cm_prove_runtime_scope_restore_region_bases();

PROOF static thm cm_prove_runtime_call_restore_region_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (caller:int)
         (st:cm_src_state) (ann:cm_annotation)
         (oldenv:int->int->cm_value) (oldfp:int)
         (oldregions:(cm_region)list) (ret:cm_type)
         (owner:int) (owner_break:int) (owner_continue:int)
         (rest:(cm_acursor)list)
         (caller_spills:(cm_spill)list)
         (saved:(cm_spill_frame)list) (returnpc:int)
         (calls:(cm_call_sim_frame)list).
         cm_ann_cursors ann ==
           CMACursor
             (CACallP caller oldenv oldfp oldregions ret)
             owner owner_break owner_continue :: rest ==>
         cm_ann_saved ann ==
           CMSpillFrame caller oldfp caller_spills :: saved ==>
         cm_ann_calls ann ==
           CMCallSimFrame (cm_state_fp st) oldfp returnpc :: calls ==>
         cm_runtime_core p fid st ann ==>
         cm_region_bases_below_equal
           (cm_state_regions
             (cm_restore_call st oldenv oldfp oldregions))
           (cm_state_regions st) (cm_state_nextgen st)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm cursor_eq = assume_rule(
      `cm_ann_cursors (ann:cm_annotation) ==
       CMACursor
         (CACallP (caller:int) (oldenv:int->int->cm_value)
           (oldfp:int) (oldregions:(cm_region)list) (ret:cm_type))
         (owner:int) (owner_break:int) (owner_continue:int) ::
       (rest:(cm_acursor)list)`);
  thm saved_eq = assume_rule(
      `cm_ann_saved (ann:cm_annotation) ==
       CMSpillFrame (caller:int) (oldfp:int)
         (caller_spills:(cm_spill)list) ::
       (saved:(cm_spill_frame)list)`);
  thm calls_eq = assume_rule(
      `cm_ann_calls (ann:cm_annotation) ==
       CMCallSimFrame (cm_state_fp (st:cm_src_state))
         (oldfp:int) (returnpc:int) ::
       (calls:(cm_call_sim_frame)list)`);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      cm_runtime_core_def)), assume_rule(
        `cm_runtime_core (p:cm_program) (fid:int)
          (st:cm_src_state) (ann:cm_annotation)`));
  thm shaped_stack = conv_rule(rewrite_conv(THM_LIST(
      cursor_eq, saved_eq, calls_eq)), conjunct2_rule(opened));
  thm call_phase = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_is_call_def)),
      `cm_phase_is_call
        (CACallP (caller:int) (oldenv:int->int->cm_value)
          (oldfp:int) (oldregions:(cm_region)list) (ret:cm_type))`));
  thm stack_body = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_runtime_stack_def, cm_cursor_phase_def, call_phase,
      cm_phase_oldregions_def, cm_phase_oldfp_def,
      cm_phase_caller_def)), shaped_stack);
  thm prefix = conjunct1_rule(stack_body);
  thm full = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
      `fid:int`, `cm_state_fp (st:cm_src_state)`,
      `cm_state_regions (st:cm_src_state)`,
      `oldregions:(cm_region)list`), cm_restore_regions_bases),
      prefix);
  thm below = match_mp_rule(specl_rule(TERM_LIST(
      `cm_restore_regions (cm_state_regions (st:cm_src_state))
        (oldregions:(cm_region)list)`,
      `cm_state_regions (st:cm_src_state)`,
      `cm_state_nextgen (st:cm_src_state)`),
      cm_region_bases_equal_below_short), full);
  thm structure = specl_rule(TERM_LIST(
      `st:cm_src_state`, `oldenv:int->int->cm_value`,
      `oldfp:int`, `oldregions:(cm_region)list`),
      cm_restore_call_structure);
  thm regions_structure =
      conjunct2_rule(conjunct2_rule(structure));
  thm target_view = apply_conversion(rewrite_conv(THM_LIST(
      regions_structure)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), below));
  return gnode_prove(root);
}
PROOF thm cm_runtime_call_restore_region_bases =
    cm_prove_runtime_call_restore_region_bases();

PROOF static int cmc_preservation_short_bases_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_short_bases_axioms_before,
      "cmc_preservation_short_bases introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_short_bases_checks =
    cmc_preservation_short_bases_final_checks();
