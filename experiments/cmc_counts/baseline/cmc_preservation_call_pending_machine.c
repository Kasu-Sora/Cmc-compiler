#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_call_pending_machine.h"

#require "cmc_preservation_call_pending_memory.c"

PROOF static size_t _cmc_preservation_call_pending_machine_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_machine_call_pending_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (callee:int)
         (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (values:(cm_value)list) (base:int).
         cm_machine_state_sim p st target frames spill_frames
           (CMIntV 8i :: CMIntV base :: CMIntV base :: values) [] ==>
         cm_function_wf p
           (inth callee (cm_program_functions p)) ==>
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         cm_state_tags_generation_below st
           (cm_state_nextgen st) ==>
         cm_values_generation_below (cm_state_nextgen st) values ==>
         cm_spill_frames_generation_below
           (cm_state_nextgen st) spill_frames ==>
         cm_tagged_span_valid st ==>
         (!addr.
            cm_live_address st addr ==>
            ~((base <= addr && addr < base + 8i))) ==>
         (!addr.
            cm_live_address st addr ==>
            ~((8i <= addr && addr < 8i + 8i))) ==>
         cm_call_frames_store_safe CMIntTy 8i frames ==>
         cm_spill_frames_store_safe p CMIntTy 8i spill_frames ==>
         base == cm_state_fp st -
           cm_frame_size (cm_program_structs p)
             (inth callee (cm_program_functions p)) ==>
         tower_signed64 (cm_state_fp st) ==>
         tower_signed64 base ==>
         cm_machine_state_sim p
           (cm_call_pending_base p callee st)
           (tvm_next_state target
             (TL (TL (tvm_stack target)))
             (tvm_calls target)
             (tower_setw (tvm_mem target) 8i base)
             (tvm_input target) (tvm_output target))
           frames
           (CMSpillFrame callee base [] :: spill_frames)
           (CMIntV base :: values) []`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term pending =
      `cm_call_pending_base (p:cm_program) (callee:int)
        (st:cm_src_state)`;
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
        (target:tvm_state) (frames:(cm_call_sim_frame)list)
        (spill_frames:(cm_spill_frame)list)
        (CMIntV 8i :: CMIntV (base:int) :: CMIntV base ::
          (values:(cm_value)list)) ([]:(int)list)`);
  thm parts = conv_rule(rewrite_conv(THM_LIST(
      cm_machine_sim_parts)), simulation);
  thm initialized = conjunct1_rule(parts);
  thm after_initialized = conjunct2_rule(parts);
  thm provenance = conjunct1_rule(after_initialized);
  thm after_provenance = conjunct2_rule(after_initialized);
  thm old_fp = conjunct1_rule(after_provenance);
  thm after_fp = conjunct2_rule(after_provenance);
  thm calls = conjunct1_rule(after_fp);
  thm after_calls = conjunct2_rule(after_fp);
  thm spills = conjunct1_rule(after_calls);
  thm after_spills = conjunct2_rule(after_calls);
  thm input_equal = conjunct1_rule(after_spills);
  thm after_input = conjunct2_rule(after_spills);
  thm output_equal = conjunct1_rule(after_input);
  thm operand = conjunct2_rule(after_input);

  thm signed_base = assume_rule(`tower_signed64 (base:int)`);
  thm fixed_base = mp_rule(spec_rule(`base:int`,
      get_tower_wrap64_fixed()), signed_base);
  thm outside8 = assume_rule(
      `!addr.
         cm_live_address (st:cm_src_state) addr ==>
         ~((8i <= addr && addr < 8i + 8i))`);
  thm initialized_store = mp_rule(mp_rule(mp_rule(
      specl_rule(TERM_LIST(
        `st:cm_src_state`, `tvm_mem (target:tvm_state)`,
        `8i:int`, `base:int`),
        get_cm_initialized_scratch_store_sim()),
      initialized), signed_base), outside8);
  thm provenance_store = mp_rule(mp_rule(mp_rule(mp_rule(
      specl_rule(TERM_LIST(
        `st:cm_src_state`, `tvm_mem (target:tvm_state)`,
        `8i:int`, `base:int`),
        get_cm_provenance_scratch_store_sim()),
      provenance), signed_base), assume_rule(
        `cm_tagged_span_valid (st:cm_src_state)`)), outside8);
  thm base_equal = assume_rule(
      `(base:int) == cm_state_fp (st:cm_src_state) -
        cm_frame_size (cm_program_structs (p:cm_program))
          (inth (callee:int) (cm_program_functions p))`);
  thm outside_frame = conv_rule(rewrite_conv(THM_LIST(base_equal)),
      assume_rule(
        `!addr.
           cm_live_address (st:cm_src_state) addr ==>
           ~((base:int) <= addr && addr < base + 8i)`));
  thm new_initialized = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `callee:int`, `st:cm_src_state`,
        `tower_setw (tvm_mem (target:tvm_state)) 8i (base:int)`),
        get_cm_call_pending_initialized_transport()),
      assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (callee:int) (cm_program_functions p))`)),
      assume_rule(
        `cm_regions_before (cm_state_regions (st:cm_src_state))
          (cm_state_nextgen st)`)), initialized_store),
      assume_rule(`tower_signed64 (cm_state_fp (st:cm_src_state))`)),
      outside_frame);
  thm new_provenance = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `callee:int`, `st:cm_src_state`,
        `tower_setw (tvm_mem (target:tvm_state)) 8i (base:int)`),
        get_cm_call_pending_provenance_transport()),
      assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (callee:int) (cm_program_functions p))`)),
      assume_rule(
        `cm_regions_before (cm_state_regions (st:cm_src_state))
          (cm_state_nextgen st)`)),
      assume_rule(
        `cm_state_tags_generation_below (st:cm_src_state)
          (cm_state_nextgen st)`)), provenance_store);

  thm stored_fp = specl_rule(TERM_LIST(
      `tvm_mem (target:tvm_state)`, `8i:int`, `base:int`),
      get_tower_getw_setw());
  stored_fp = conv_rule(rewrite_conv(THM_LIST(fixed_base)), stored_fp);
  thm pending_fp = conjunct1_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `callee:int`, `st:cm_src_state`),
      cm_call_pending_structure));
  thm base_pending_fp =
      trans_rule(base_equal, sym_rule(pending_fp));
  thm new_fp = trans_rule(stored_fp, base_pending_fp);

  thm call_store_rule = specl_rule(TERM_LIST(
      `CMIntTy:cm_type`, `8i:int`, `base:int`,
      `tvm_mem (target:tvm_state)`,
      `frames:(cm_call_sim_frame)list`,
      `tvm_calls (target:tvm_state)`),
      get_cm_call_frames_store_sim());
  thm new_calls = match_mp_rule(match_mp_rule(call_store_rule, calls),
      assume_rule(
        `cm_call_frames_store_safe CMIntTy 8i
          (frames:(cm_call_sim_frame)list)`));
  new_calls = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_store_mem_def(), get_cm_type_int_char_distinct(), fixed_base)),
      new_calls);

  thm spills_store = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `st:cm_src_state`,
        `tvm_mem (target:tvm_state)`, `8i:int`, `base:int`,
        `spill_frames:(cm_spill_frame)list`),
        get_cm_spill_frames_scratch_store_sim()),
      spills), assume_rule(
        `cm_spill_frames_store_safe (p:cm_program) CMIntTy 8i
          (spill_frames:(cm_spill_frame)list)`)), signed_base);
  thm transported_spills = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `spill_frames:(cm_spill_frame)list`, `p:cm_program`,
        `st:cm_src_state`, pending,
        `tower_setw (tvm_mem (target:tvm_state)) 8i (base:int)`,
        `cm_state_nextgen (st:cm_src_state)`),
        cm_spill_frames_sim_bases),
      specl_rule(TERM_LIST(`p:cm_program`, `callee:int`,
        `st:cm_src_state`), cm_call_pending_regions_bases)),
      assume_rule(
        `cm_spill_frames_generation_below
          (cm_state_nextgen (st:cm_src_state))
          (spill_frames:(cm_spill_frame)list)`)), spills_store);
  thm new_spills = eq_mp_rule(sym_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_spill_frames_sim_def, cm_spill_list_sim_def,
        cm_spill_frame_fid_def, cm_spill_frame_fp_def,
        cm_spill_frame_spills_def)),
      `cm_spill_frames_sim (p:cm_program) ${pending:cm_src_state}
        (tower_setw (tvm_mem (target:tvm_state)) 8i (base:int))
        (CMSpillFrame (callee:int) base [] ::
          (spill_frames:(cm_spill_frame)list))`)), transported_spills);

  thm old_stack = conv_rule(rewrite_conv(THM_LIST(
      cm_operand_suffix_sim_def)), operand);
  thm tail_stack = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(old_stack, cm_encode_values_def,
        get_theorem_by_name("APPEND"), get_theorem_by_name("TL"))),
      `TL (TL (tvm_stack (target:tvm_state))) ==
       cm_encode_values (st:cm_src_state)
         (CMIntV (base:int) :: (values:(cm_value)list)) ++ []`));
  thm old_operand = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_operand_suffix_sim_def)),
      `cm_operand_suffix_sim (st:cm_src_state)
        (CMIntV (base:int) :: (values:(cm_value)list))
        ([]:(int)list) (TL (TL (tvm_stack (target:tvm_state))))`)),
      tail_stack);
  thm old_values_below = assume_rule(
      `cm_values_generation_below
        (cm_state_nextgen (st:cm_src_state))
        (values:(cm_value)list)`);
  thm values_below_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_values_generation_below_def, cm_value_generation_below_def)),
      `cm_values_generation_below
        (cm_state_nextgen (st:cm_src_state))
        (CMIntV (base:int) :: (values:(cm_value)list))`);
  thm values_below =
      eq_mp_rule(sym_rule(values_below_view), old_values_below);
  thm new_operand = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `st:cm_src_state`, pending,
        `CMIntV (base:int) :: (values:(cm_value)list)`,
        `[]:(int)list`, `TL (TL (tvm_stack (target:tvm_state)))`,
        `cm_state_nextgen (st:cm_src_state)`),
        cm_operand_suffix_sim_bases),
      specl_rule(TERM_LIST(`p:cm_program`, `callee:int`,
        `st:cm_src_state`), cm_call_pending_regions_bases)),
      values_below), old_operand);

  thm pending_structure = specl_rule(TERM_LIST(
      `p:cm_program`, `callee:int`, `st:cm_src_state`),
      cm_call_pending_structure);
  thm pending_input = conjunct1_rule(conjunct2_rule(
      conjunct2_rule(conjunct2_rule(pending_structure))));
  thm pending_output = conjunct2_rule(conjunct2_rule(
      conjunct2_rule(conjunct2_rule(pending_structure))));
  thm new_input = trans_rule(input_equal, sym_rule(pending_input));
  thm new_output = trans_rule(output_equal, sym_rule(pending_output));

  thm result = conj_rule(new_initialized,
      conj_rule(new_provenance,
      conj_rule(new_fp,
      conj_rule(new_calls,
      conj_rule(new_spills,
      conj_rule(new_input,
      conj_rule(new_output, new_operand)))))));
  thm_list final_rules = THM_LIST(
      cm_machine_sim_parts, get_tvm_next_state_def(),
      get_tvm_state_selectors_def());
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(final_rules));
  ACCEPT_TAC(reduced,
      conv_rule(reduce_rewrite_conv(final_rules), result));
  return gnode_prove(root);
}
PROOF thm cm_machine_call_pending_store =
    cm_prove_machine_call_pending_store();

PROOF thm get_cm_machine_call_pending_store(void) {
  return cm_machine_call_pending_store;
}

PROOF static int cmc_preservation_call_pending_machine_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_call_pending_machine_axioms_before,
      "cmc_preservation_call_pending_machine introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_machine_call_pending_store)) == 0,
      "cm_machine_call_pending_store has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_call_pending_machine_checks =
    cmc_preservation_call_pending_machine_final_checks();
