#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_spill_holds_safety.h"
#include "cmc_preservation_invariant.h"
#include "cmc_sim.h"

#require "cmc_preservation_invariant.c"
#require "cmc_sim.c"

PROOF static size_t _cmc_preservation_spill_holds_safety_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_spills_within_holds_bounds(void) {
  gnode root = gnode_new_with_ccl(
      `!(spills:(cm_spill)list). !(p:cm_program) (fid:int) (fp:int)
         (oldfp:int) (slot:int) (held_value:cm_value).
         cm_spills_within_frame p fid fp oldfp spills ==>
         cm_spill_holds slot held_value spills ==>
         fp + cm_temp_offset p fid 0i <=
           fp + cm_temp_offset p fid slot &&
         fp + cm_temp_offset p fid slot + 8i <= oldfp`);
  gnode_list cases = INDUCT_TAC(root, `spills:(cm_spill)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_spill_holds_def)), assume_rule(
          `cm_spill_holds (slot:int) (held_value:cm_value)
            ([]:(cm_spill)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm within = conv_rule(rewrite_conv(THM_LIST(
        cm_spills_within_frame_def)), assume_rule(
          `cm_spills_within_frame (p:cm_program) (fid:int) (fp:int)
            (oldfp:int)
            ((a0:cm_spill) :: (a1:(cm_spill)list))`));
    thm holds = assume_rule(
        `cm_spill_holds (slot:int) (held_value:cm_value)
          ((a0:cm_spill) :: (a1:(cm_spill)list))`);
    gnode_list selected_cases = BOOL_CASES_TAC(
        leaf, `cm_spill_slot (a0:cm_spill) == (slot:int)`,
        "Hselected");
    {
      thm selected = assume_rule(
          `cm_spill_slot (a0:cm_spill) == (slot:int)`);
      thm result = conv_rule(rewrite_conv(THM_LIST(selected)),
          conj_rule(conjunct1_rule(within),
            conjunct1_rule(conjunct2_rule(within))));
      ACCEPT_TAC(selected_cases[0], result);
    }
    {
      thm not_selected = assume_rule(
          `~(cm_spill_slot (a0:cm_spill) == (slot:int))`);
      thm tail_holds = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_spill_holds_def, not_selected)), holds);
      thm ih = specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `fp:int`, `oldfp:int`,
          `slot:int`, `held_value:cm_value`),
          assume_rule(goal_lasmps(selected_cases[1]->g)[0].tm));
      thm result = match_mp_rule(match_mp_rule(
          ih, conjunct2_rule(conjunct2_rule(within))), tail_holds);
      ACCEPT_TAC(selected_cases[1], result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_spills_within_holds_bounds =
    cm_prove_spills_within_holds_bounds();

PROOF static thm cm_prove_runtime_spill_holds_address_safe(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (cursors:(cm_acursor)list) (fid:int) (fp:int)
         (active:(cm_region)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)
         (slot:int) (held_value:cm_value) (address:int).
         cm_runtime_stack p all_regions fid fp active cursors
           spills saved calls ==>
         cm_spill_holds slot held_value spills ==>
         0i <= fid ==>
         address == fp + cm_temp_offset p fid slot ==>
         tower_signed64 fp &&
         tower_signed64 (cm_temp_offset p fid slot) &&
         tower_signed64 address &&
         tower_word_valid address`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_regions = GEN_TAC(with_program, "all_regions");
  gnode_list cases = INDUCT_TAC(
      with_regions, `cursors:(cm_acursor)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_runtime_stack_def)), assume_rule(
          `cm_runtime_stack
            (p:cm_program) (all_regions:(cm_region)list)
            (fid:int) (fp:int) (active:(cm_region)list)
            ([]:(cm_acursor)list) (spills:(cm_spill)list)
            (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term phase = `cm_cursor_phase (a0:cm_acursor)`;
    term oldfp = `cm_phase_oldfp ${phase:cm_aphase}`;
    term offset =
        `cm_temp_offset (p:cm_program) (fid:int) (slot:int)`;
    term temp_base =
        `(fp:int) + cm_temp_offset (p:cm_program) (fid:int) 0i`;
    thm stack = assume_rule(
        `cm_runtime_stack (p:cm_program)
          (all_regions:(cm_region)list) (fid:int) (fp:int)
          (active:(cm_region)list)
          ((a0:cm_acursor) :: (a1:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`);
    thm holds = assume_rule(
        `cm_spill_holds (slot:int) (held_value:cm_value)
          (spills:(cm_spill)list)`);
    thm fid_nonnegative = assume_rule(`0i <= (fid:int)`);
    thm address_equal = assume_rule(
        `(address:int) == (fp:int) + ${offset:int}`);
    gnode_list call_cases = BOOL_CASES_TAC(
        leaf, `cm_phase_is_call ${phase:cm_aphase}`, "Hcall");
    {
      thm call = assume_rule(`cm_phase_is_call ${phase:cm_aphase}`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_runtime_stack_def, call)), stack);
      thm segment = conv_rule(rewrite_conv(THM_LIST(
          cm_frame_segment_def)), mp_rule(taut_rule(mk_imp(
            concl(opened),
            `cm_frame_segment (p:cm_program) (fid:int) (fp:int)
              ${oldfp:int}`)), opened));
      thm within = mp_rule(taut_rule(mk_imp(concl(opened),
          `cm_spills_within_frame (p:cm_program) (fid:int)
            (fp:int) ${oldfp:int} (spills:(cm_spill)list)`)), opened);
      thm held_bounds = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
          `spills:(cm_spill)list`, `p:cm_program`, `fid:int`, `fp:int`,
          oldfp, `slot:int`, `held_value:cm_value`),
          cm_spills_within_holds_bounds), within), holds);
      thm static_bounds = mp_rule(taut_rule(mk_imp(
          concl(segment),
          `16i <= cm_static_size (p:cm_program) &&
           cm_static_size p <= (fp:int)`)), segment);
      thm fp_nonnegative = mp_rule(mp_rule(int_arith_rule(
          `16i <= cm_static_size (p:cm_program) ==>
           cm_static_size p <= (fp:int) ==> 0i <= fp`),
          conjunct1_rule(static_bounds)), conjunct2_rule(static_bounds));
      thm temp_lower = mp_rule(taut_rule(mk_imp(
          concl(segment), `(fp:int) + 8i <= ${temp_base:int}`)),
          segment);
      thm old_upper = mp_rule(taut_rule(mk_imp(
          concl(segment), `${oldfp:int} <= 1048576i`)), segment);
      thm frame_facts = conj_rule(fp_nonnegative,
          conj_rule(temp_lower, old_upper));
      thm spill_lower = conv_rule(rewrite_conv(THM_LIST(
          sym_rule(address_equal))), conjunct1_rule(held_bounds));
      thm raw_spill_upper = conjunct2_rule(held_bounds);
      thm spill_upper = mp_rule(mp_rule(int_arith_rule(
          `(fp:int) + ${offset:int} + 8i <= ${oldfp:int} ==>
           (address:int) == fp + ${offset:int} ==>
           address + 8i <= ${oldfp:int}`),
          raw_spill_upper), address_equal);
      thm spill_facts = conj_rule(spill_lower, spill_upper);
      term expanded =
          `--9223372036854775808i <= (fp:int) &&
           fp <= 9223372036854775807i &&
           --9223372036854775808i <= ${offset:int} &&
           ${offset:int} <= 9223372036854775807i &&
           --9223372036854775808i <= (address:int) &&
           address <= 9223372036854775807i &&
           0i <= address && address + 7i < 1048576i`;
      thm numeric = int_arith_rule(
          `0i <= (fp:int) &&
           fp + 8i <= ${temp_base:int} &&
           ${oldfp:int} <= 1048576i ==>
           ${temp_base:int} <= (address:int) &&
           address + 8i <= ${oldfp:int} ==>
           (address:int) == fp + ${offset:int} ==>
           ${expanded:bool}`);
      numeric = mp_rule(numeric, frame_facts);
      numeric = mp_rule(numeric, spill_facts);
      numeric = mp_rule(numeric, address_equal);
      thm target_view = apply_conversion(
          rewrite_conv(THM_LIST(
            get_tower_signed64_def(), get_tower_word_valid_def())),
          goal_ccl(call_cases[0]->g));
      struct dest_eq_results target_parts = dest_eq(concl(target_view));
      thm regrouped = mp_rule(
          taut_rule(mk_imp(concl(numeric), target_parts.tm2)), numeric);
      ACCEPT_TAC(call_cases[0],
          eq_mp_rule(sym_rule(target_view), regrouped));
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
        thm recursive = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_runtime_stack_def, not_call, scope)), stack);
        thm induction = assume_rule(
            goal_lasmps(scope_cases[0]->g)[0].tm);
        thm result = specl_rule(TERM_LIST(
            `fid:int`, `fp:int`,
            `cm_phase_oldregions ${phase:cm_aphase}`,
            `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
            `calls:(cm_call_sim_frame)list`, `slot:int`,
            `held_value:cm_value`, `address:int`), induction);
        result = match_mp_rule(result,
            conjunct2_rule(conjunct2_rule(recursive)));
        result = match_mp_rule(result, holds);
        result = match_mp_rule(result, fid_nonnegative);
        result = match_mp_rule(result, address_equal);
        ACCEPT_TAC(scope_cases[0], result);
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
          thm fid_halt = mp_rule(taut_rule(mk_imp(
              concl(opened), `(fid:int) == --1i`)), opened);
          CONTR_TAC(halt_cases[0], mp_rule(mp_rule(int_arith_rule(
              `(fid:int) == --1i ==> 0i <= fid ==> false`),
              fid_halt), fid_nonnegative));
        }
        {
          thm not_halt = assume_rule(
              `~cm_phase_is_halt ${phase:cm_aphase}`);
          thm recursive = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, not_halt)),
              stack);
          thm induction = assume_rule(
              goal_lasmps(halt_cases[1]->g)[0].tm);
          thm result = specl_rule(TERM_LIST(
              `fid:int`, `fp:int`, `active:(cm_region)list`,
              `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`, `slot:int`,
              `held_value:cm_value`, `address:int`), induction);
          result = match_mp_rule(result, recursive);
          result = match_mp_rule(result, holds);
          result = match_mp_rule(result, fid_nonnegative);
          result = match_mp_rule(result, address_equal);
          ACCEPT_TAC(halt_cases[1], result);
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_runtime_spill_holds_address_safe =
    cm_prove_runtime_spill_holds_address_safe();

PROOF thm get_cm_spills_within_holds_bounds(void) {
  return cm_spills_within_holds_bounds;
}
PROOF thm get_cm_runtime_spill_holds_address_safe(void) {
  return cm_runtime_spill_holds_address_safe;
}

PROOF static int cmc_preservation_spill_holds_safety_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_spill_holds_safety_axioms_before,
      "cmc_preservation_spill_holds_safety introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_spills_within_holds_bounds)) == 0 &&
      vector_size(hyp(cm_runtime_spill_holds_address_safe)) == 0,
      "held spill safety theorem has assumptions");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_spill_holds_safety_checked =
    cmc_preservation_spill_holds_safety_final_checks();
