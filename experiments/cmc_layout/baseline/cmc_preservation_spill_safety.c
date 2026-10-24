#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_invariant.h"
#include "cmc_preservation_spill_safety.h"

#require "cmc_preservation_invariant.c"

PROOF static size_t _cmc_preservation_spill_safety_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_runtime_spill_metadata_safe(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (cursors:(cm_acursor)list) (fid:int) (fp:int)
         (active:(cm_region)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)
         (slot:int) (v:cm_value) (address:int).
         cm_runtime_stack p all_regions fid fp active cursors
           (cm_spill_put slot v spills) saved calls ==>
         0i <= fid ==>
         address == fp + cm_temp_offset p fid slot ==>
         cm_range_disjoint address 8i 8i 8i &&
         cm_call_frames_store_safe CMIntTy address calls &&
         cm_spill_frames_store_safe p CMIntTy address saved`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_regions = GEN_TAC(with_program, "all_regions");
  gnode_list cases = INDUCT_TAC(
      with_regions, `cursors:(cm_acursor)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_runtime_stack_def)), assume_rule(
          `cm_runtime_stack (p:cm_program)
            (all_regions:(cm_region)list) (fid:int) (fp:int)
            (active:(cm_region)list) ([]:(cm_acursor)list)
            (cm_spill_put (slot:int) (v:cm_value)
              (spills:(cm_spill)list))
            (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term phase = `cm_cursor_phase (a0:cm_acursor)`;
    term temp_base =
        `(fp:int) + cm_temp_offset (p:cm_program) (fid:int) 0i`;
    term oldfp = `cm_phase_oldfp ${phase:cm_aphase}`;
    thm stack = assume_rule(
        `cm_runtime_stack (p:cm_program)
          (all_regions:(cm_region)list) (fid:int) (fp:int)
          (active:(cm_region)list)
          ((a0:cm_acursor) :: (a1:(cm_acursor)list))
          (cm_spill_put (slot:int) (v:cm_value)
            (spills:(cm_spill)list))
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`);
    thm fid_nonnegative = assume_rule(`0i <= (fid:int)`);
    thm address_equal = assume_rule(
        `(address:int) ==
         (fp:int) + cm_temp_offset (p:cm_program) (fid:int)
           (slot:int)`);
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
      thm within = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_spills_within_frame_def, cm_spill_put_def,
          cm_spill_slot_def, sym_rule(address_equal))),
          mp_rule(taut_rule(mk_imp(concl(opened),
            `cm_spills_within_frame (p:cm_program) (fid:int)
              (fp:int) ${oldfp:int}
              (cm_spill_put (slot:int) (v:cm_value)
                (spills:(cm_spill)list))`)), opened));
      thm temp_lower = mp_rule(taut_rule(mk_imp(
          concl(segment),
          `(fp:int) + 8i <= ${temp_base:int}`)), segment);
      thm address_lower = mp_rule(taut_rule(mk_imp(
          concl(within),
          `${temp_base:int} <= (address:int)`)), within);
      thm address_upper = mp_rule(mp_rule(int_arith_rule(
          `(address:int) ==
             (fp:int) + cm_temp_offset (p:cm_program) (fid:int)
               (slot:int) ==>
           fp + cm_temp_offset p fid slot + 8i <= ${oldfp:int} ==>
           address + 8i <= ${oldfp:int}`),
          address_equal),
          conjunct1_rule(conjunct2_rule(within)));
      thm fp_bounds = match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `all_regions:(cm_region)list`,
          `(a0:cm_acursor) :: (a1:(cm_acursor)list)`,
          `fid:int`, `fp:int`, `active:(cm_region)list`,
          `cm_spill_put (slot:int) (v:cm_value)
            (spills:(cm_spill)list)`,
          `saved:(cm_spill_frame)list`,
          `calls:(cm_call_sim_frame)list`),
          cm_runtime_stack_fp_bounds), stack);
      thm reserved_raw = mp_rule(mp_rule(mp_rule(
          int_arith_rule(
            `16i <= cm_static_size (p:cm_program) &&
             cm_static_size p <= (fp:int) && fp <= 1048576i ==>
             fp + 8i <= (${temp_base:int}) ==>
             (${temp_base:int}) <= (address:int) ==>
             address + 8i <= 8i || 8i + 8i <= address`),
          fp_bounds), temp_lower), address_lower);
      thm reserved_safe = eq_mp_rule(sym_rule(apply_conversion(
          rewrite_conv(THM_LIST(cm_range_disjoint_def)),
          `cm_range_disjoint (address:int) 8i 8i 8i`)),
          reserved_raw);

      thm recursive = mp_rule(taut_rule(mk_imp(concl(opened),
          `cm_runtime_stack (p:cm_program)
            (all_regions:(cm_region)list)
            (cm_phase_caller ${phase:cm_aphase}) ${oldfp:int}
            (cm_phase_oldregions ${phase:cm_aphase})
            (a1:(cm_acursor)list)
            (cm_spill_frame_spills
              (HD (saved:(cm_spill_frame)list)))
            (TL saved) (TL (calls:(cm_call_sim_frame)list))`)),
          opened);
      thm outer_lower = match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `all_regions:(cm_region)list`,
          `a1:(cm_acursor)list`,
          `cm_phase_caller ${phase:cm_aphase}`, oldfp,
          `cm_phase_oldregions ${phase:cm_aphase}`,
          `cm_spill_frame_spills
            (HD (saved:(cm_spill_frame)list))`,
          `TL (saved:(cm_spill_frame)list)`,
          `TL (calls:(cm_call_sim_frame)list)`),
          cm_runtime_stack_lower), recursive);
      thm tail_calls_lower = conjunct1_rule(outer_lower);
      thm outer_current_spills = conjunct1_rule(
          conjunct2_rule(outer_lower));
      thm outer_saved_lower = conjunct2_rule(
          conjunct2_rule(outer_lower));

      thm tail_calls_range = match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(`address:int`, `8i:int`, oldfp,
            `TL (calls:(cm_call_sim_frame)list)`),
            cm_call_lower_range_safe), address_upper),
          tail_calls_lower);
      thm calls_nonempty = mp_rule(taut_rule(mk_imp(concl(opened),
          `~((calls:(cm_call_sim_frame)list) == [])`)), opened);
      thm call_base = mp_rule(taut_rule(mk_imp(concl(opened),
          `cm_call_sim_base
             (HD (calls:(cm_call_sim_frame)list)) == (fp:int)`)),
          opened);
      thm head_call_raw = mp_rule(mp_rule(mp_rule(
          int_arith_rule(
            `cm_call_sim_base
               (HD (calls:(cm_call_sim_frame)list)) == (fp:int) ==>
             fp + 8i <= (${temp_base:int}) ==>
             (${temp_base:int}) <= (address:int) ==>
             address + 8i <= cm_call_sim_base (HD calls) ||
             cm_call_sim_base (HD calls) + 8i <= address`),
          call_base), temp_lower), address_lower);
      thm head_call_range = eq_mp_rule(sym_rule(apply_conversion(
          rewrite_conv(THM_LIST(cm_range_disjoint_def)),
          `cm_range_disjoint (address:int) 8i
            (cm_call_sim_base
              (HD (calls:(cm_call_sim_frame)list))) 8i`)),
          head_call_raw);
      term call_cons_term =
          `cm_call_frames_range_safe (address:int) 8i
            (HD (calls:(cm_call_sim_frame)list) :: TL calls)`;
      thm call_cons = eq_mp_rule(sym_rule(apply_conversion(
          rewrite_conv(THM_LIST(cm_call_frames_range_safe_def)),
          call_cons_term)), conj_rule(head_call_range, tail_calls_range));
      thm calls_shape = match_mp_rule(
          ispec_rule(`calls:(cm_call_sim_frame)list`,
            get_theorem_by_name("CONS_HD_TL")), calls_nonempty);
      thm all_calls_range = eq_mp_rule(sym_rule(ap_term_rule(
          `cm_call_frames_range_safe (address:int) 8i`,
          calls_shape)), call_cons);
      thm store_width_reduction = apply_conversion(
          reduce_rewrite_conv(THM_LIST(get_cm_store_width_def(),
            get_cm_type_int_char_distinct())),
          `(address:int) + cm_store_width CMIntTy <= address + 8i`);
      thm store_width = eq_mp_rule(sym_rule(store_width_reduction),
          int_arith_rule(`(address:int) + 8i <= address + 8i`));
      thm all_calls_safe = match_mp_rule(match_mp_rule(
          match_mp_rule(specl_rule(TERM_LIST(
            `address:int`, `8i:int`, `address:int`,
            `CMIntTy:cm_type`, `calls:(cm_call_sim_frame)list`),
            cm_call_frames_range_subrange),
            int_arith_rule(`(address:int) <= address`)),
          store_width), all_calls_range);

      thm saved_nonempty = mp_rule(taut_rule(mk_imp(concl(opened),
          `~((saved:(cm_spill_frame)list) == [])`)), opened);
      thm saved_fid = mp_rule(taut_rule(mk_imp(concl(opened),
          `cm_spill_frame_fid
             (HD (saved:(cm_spill_frame)list)) ==
           cm_phase_caller ${phase:cm_aphase}`)), opened);
      thm saved_fp = mp_rule(taut_rule(mk_imp(concl(opened),
          `cm_spill_frame_fp
             (HD (saved:(cm_spill_frame)list)) == ${oldfp:int}`)),
          opened);
      term saved_head_term =
          `cm_spill_list_lower (p:cm_program) ${oldfp:int}
            (cm_spill_frame_fid
              (HD (saved:(cm_spill_frame)list)))
            (cm_spill_frame_fp (HD saved))
            (cm_spill_frame_spills (HD saved))`;
      thm saved_head_reduction = apply_conversion(
          rewrite_conv(THM_LIST(saved_fid, saved_fp)),
          saved_head_term);
      thm saved_head_lower = eq_mp_rule(
          sym_rule(saved_head_reduction), outer_current_spills);
      term saved_cons_term =
          `cm_spill_frames_lower (p:cm_program) ${oldfp:int}
            (HD (saved:(cm_spill_frame)list) :: TL saved)`;
      thm saved_cons = eq_mp_rule(sym_rule(apply_conversion(
          rewrite_conv(THM_LIST(cm_spill_frames_lower_def)),
          saved_cons_term)),
          conj_rule(saved_head_lower, outer_saved_lower));
      thm saved_shape = match_mp_rule(
          ispec_rule(`saved:(cm_spill_frame)list`,
            get_theorem_by_name("CONS_HD_TL")), saved_nonempty);
      thm all_saved_lower = eq_mp_rule(sym_rule(ap_term_rule(
          `cm_spill_frames_lower (p:cm_program) ${oldfp:int}`,
          saved_shape)), saved_cons);
      thm all_saved_range = match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(`p:cm_program`, `address:int`,
            `8i:int`, oldfp, `saved:(cm_spill_frame)list`),
            cm_spill_frames_lower_range_safe), address_upper),
          all_saved_lower);
      thm all_saved_safe = match_mp_rule(match_mp_rule(
          match_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `address:int`, `8i:int`,
            `address:int`, `CMIntTy:cm_type`,
            `saved:(cm_spill_frame)list`),
            cm_spill_frames_range_subrange),
            int_arith_rule(`(address:int) <= address`)),
          store_width), all_saved_range);
      ACCEPT_TAC(call_cases[0], conj_rule(reserved_safe,
          conj_rule(all_calls_safe, all_saved_safe)));
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
        thm recursive = conjunct2_rule(conjunct2_rule(opened));
        thm induction = assume_rule(goal_lasmps(scope_cases[0]->g)[0].tm);
        thm result = match_mp_rule(match_mp_rule(match_mp_rule(
            specl_rule(TERM_LIST(`fid:int`, `fp:int`,
              `cm_phase_oldregions ${phase:cm_aphase}`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`, `slot:int`,
              `v:cm_value`, `address:int`), induction),
            recursive), fid_nonnegative), address_equal);
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
          thm fid_halt = mp_rule(taut_rule(mk_imp(concl(opened),
              `(fid:int) == --1i`)), opened);
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
          thm result = match_mp_rule(match_mp_rule(match_mp_rule(
              specl_rule(TERM_LIST(`fid:int`, `fp:int`,
                `active:(cm_region)list`,
                `spills:(cm_spill)list`,
                `saved:(cm_spill_frame)list`,
                `calls:(cm_call_sim_frame)list`, `slot:int`,
                `v:cm_value`, `address:int`), induction),
              recursive), fid_nonnegative), address_equal);
          ACCEPT_TAC(halt_cases[1], result);
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_runtime_spill_metadata_safe =
    cm_prove_runtime_spill_metadata_safe();


PROOF static thm cm_prove_runtime_spill_address_safe(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (cursors:(cm_acursor)list) (fid:int) (fp:int)
         (active:(cm_region)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)
         (slot:int) (v:cm_value) (address:int).
         cm_runtime_stack p all_regions fid fp active cursors
           (cm_spill_put slot v spills) saved calls ==>
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
            ([]:(cm_acursor)list)
            (cm_spill_put (slot:int) (v:cm_value)
              (spills:(cm_spill)list))
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
          (cm_spill_put (slot:int) (v:cm_value)
            (spills:(cm_spill)list))
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`);
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
      thm within = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_spills_within_frame_def, cm_spill_put_def,
          cm_spill_slot_def, sym_rule(address_equal))),
          mp_rule(taut_rule(mk_imp(concl(opened),
            `cm_spills_within_frame (p:cm_program) (fid:int)
              (fp:int) ${oldfp:int}
              (cm_spill_put (slot:int) (v:cm_value)
                (spills:(cm_spill)list))`)), opened));
      thm static_bounds = mp_rule(taut_rule(mk_imp(
          concl(segment),
          `16i <= cm_static_size (p:cm_program) &&
           cm_static_size p <= (fp:int)`)), segment);
      thm fp_nonnegative = mp_rule(mp_rule(int_arith_rule(
          `16i <= cm_static_size (p:cm_program) ==>
           cm_static_size p <= (fp:int) ==> 0i <= fp`),
          conjunct1_rule(static_bounds)), conjunct2_rule(static_bounds));
      thm temp_lower = mp_rule(taut_rule(mk_imp(
          concl(segment),
          `(fp:int) + 8i <= ${temp_base:int}`)), segment);
      thm old_upper = mp_rule(taut_rule(mk_imp(
          concl(segment),
          `${oldfp:int} <= 1048576i`)), segment);
      thm frame_facts = conj_rule(fp_nonnegative,
          conj_rule(temp_lower, old_upper));
      thm spill_lower = mp_rule(taut_rule(mk_imp(
          concl(within),
          `${temp_base:int} <= (address:int)`)), within);
      thm raw_spill_upper = mp_rule(taut_rule(mk_imp(
          concl(within),
          `(fp:int) + ${offset:int} + 8i <= ${oldfp:int}`)), within);
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
        thm result = match_mp_rule(match_mp_rule(match_mp_rule(
            specl_rule(TERM_LIST(
              `fid:int`, `fp:int`,
              `cm_phase_oldregions ${phase:cm_aphase}`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`, `slot:int`,
              `v:cm_value`, `address:int`), induction),
            conjunct2_rule(conjunct2_rule(recursive))),
            fid_nonnegative), address_equal);
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
          thm result = match_mp_rule(match_mp_rule(match_mp_rule(
              specl_rule(TERM_LIST(
                `fid:int`, `fp:int`, `active:(cm_region)list`,
                `spills:(cm_spill)list`,
                `saved:(cm_spill_frame)list`,
                `calls:(cm_call_sim_frame)list`, `slot:int`,
                `v:cm_value`, `address:int`), induction),
              recursive), fid_nonnegative), address_equal);
          ACCEPT_TAC(halt_cases[1], result);
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_runtime_spill_address_safe =
    cm_prove_runtime_spill_address_safe();

PROOF static thm cm_prove_runtime_spill_outside_live(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state)
         (cursors:(cm_acursor)list) (fid:int) (fp:int)
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)
         (slot:int) (v:cm_value) (address:int).
         cm_runtime_stack p (cm_state_regions st) fid fp
           (cm_state_regions st) cursors
           (cm_spill_put slot v spills) saved calls ==>
         address == fp + cm_temp_offset p fid slot ==>
         !addr.
           cm_live_address st addr ==>
           ~(address <= addr && addr < address + 8i)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm stack = assume_rule(
      `cm_runtime_stack (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int) (fp:int)
        (cm_state_regions st) (cursors:(cm_acursor)list)
        (cm_spill_put (slot:int) (v:cm_value)
          (spills:(cm_spill)list))
        (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`);
  thm address_equal = assume_rule(
      `(address:int) ==
       (fp:int) + cm_temp_offset (p:cm_program) (fid:int)
         (slot:int)`);
  thm live_exists = conv_rule(rewrite_conv(THM_LIST(
      cm_live_address_def)), assume_rule(
        `cm_live_address (st:cm_src_state) (addr:int)`));
  thm body = assume_rule(
      `MEM (region:cm_region) (cm_state_regions (st:cm_src_state)) &&
       cm_region_live region &&
       cm_region_base (cm_state_regions st)
           (cm_region_gen region) + cm_region_lo region <= (addr:int) &&
       addr < cm_region_base (cm_state_regions st)
           (cm_region_gen region) + cm_region_hi region`);
  thm region_safe = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(`p:cm_program`,
        `cm_state_regions (st:cm_src_state)`,
        `cursors:(cm_acursor)list`, `fid:int`, `fp:int`,
        `cm_state_regions st`,
        `cm_spill_put (slot:int) (v:cm_value)
          (spills:(cm_spill)list)`,
        `saved:(cm_spill_frame)list`,
        `calls:(cm_call_sim_frame)list`, `region:cm_region`),
        cm_runtime_stack_region_safe), stack),
      conjunct1_rule(body)),
      conjunct1_rule(conjunct2_rule(body)));
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_region_runtime_safe_def,
      conjunct1_rule(conjunct2_rule(body)),
      cm_machine_range_safe_def, cm_spill_frames_range_safe_def,
      cm_spill_frame_fid_def, cm_spill_frame_fp_def,
      cm_spill_frame_spills_def, cm_spill_list_range_safe_def,
      cm_spill_put_def, cm_spill_slot_def,
      sym_rule(address_equal))), region_safe);
  term region_base =
      `cm_region_base (cm_state_regions (st:cm_src_state))
        (cm_region_gen (region:cm_region))`;
  term region_start = `${region_base:int} + cm_region_lo (region:cm_region)`;
  term region_width =
      `cm_region_hi (region:cm_region) - cm_region_lo region`;
  thm disjoint = mp_rule(taut_rule(mk_imp(concl(opened),
      `cm_range_disjoint ${region_start:int} ${region_width:int}
        (address:int) 8i`)), opened);
  disjoint = conv_rule(rewrite_conv(THM_LIST(
      cm_range_disjoint_def)), disjoint);
  thm outside = mp_rule(mp_rule(mp_rule(int_arith_rule(
      `(${region_start:int}) <= (addr:int) ==>
       addr < ${region_base:int} + cm_region_hi (region:cm_region) ==>
       (${region_start:int}) + (${region_width:int}) <=
           (address:int) || address + 8i <= ${region_start:int} ==>
       ~((address:int) <= addr && addr < address + 8i)`),
      conjunct1_rule(conjunct2_rule(conjunct2_rule(body)))),
      conjunct2_rule(conjunct2_rule(conjunct2_rule(body)))),
      disjoint);
  thm witness = choose_rule(`region:cm_region`, live_exists, outside);
  CONTR_TAC(leaf, contra(witness, assume_rule(
      `(address:int) <= (addr:int) && addr < address + 8i`)));
  return gnode_prove(root);
}
PROOF thm cm_runtime_spill_outside_live =
    cm_prove_runtime_spill_outside_live();

PROOF thm get_cm_runtime_spill_metadata_safe(void) {
  return cm_runtime_spill_metadata_safe;
}
PROOF thm get_cm_runtime_spill_address_safe(void) {
  return cm_runtime_spill_address_safe;
}
PROOF thm get_cm_runtime_spill_outside_live(void) {
  return cm_runtime_spill_outside_live;
}

PROOF static int cmc_preservation_spill_safety_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_spill_safety_axioms_before,
      "cmc_preservation_spill_safety introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_spill_safety_checks =
    cmc_preservation_spill_safety_final_checks();
