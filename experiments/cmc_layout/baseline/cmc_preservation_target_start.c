#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "userlib/proof_patterns.h"
#include "cmc_preservation_target_start.h"
#include "cmc_preservation_target_call_complete.h"
#include "cmc_preservation_target_ready.h"
#include "cmc_preservation_invariant_step.h"
#include "cmc_preservation_invariant_transition.h"
#include "cmc_preservation_generation_state.h"
#include "cmc_preservation_tagged.h"
#include "cmc_preservation_memory.h"
#include "cmc_preservation_machine_store.h"
#include "cmc_preservation_code.h"
#include "cmc_preservation_tvm.h"

#require "userlib/proof_patterns.c"
#require "cmc_preservation_target_call_complete.c"
#require "cmc_preservation_target_ready.c"
#require "cmc_preservation_invariant_step.c"
#require "cmc_preservation_invariant_transition.c"
#require "cmc_preservation_generation_state.c"
#require "cmc_preservation_tagged.c"
#require "cmc_preservation_memory.c"
#require "cmc_preservation_machine_store.c"

PROOF static size_t _cmc_preservation_target_start_axioms_before =
    vector_size(get_all_axioms());
PROOF static thm cm_start_pick(
    const thm premise, const term conclusion) {
  return mp_rule(taut_rule(mk_imp(concl(premise), conclusion)), premise);
}

PROOF static thm cm_prove_start_prelude_sites(void) {
  term code = `cm_model_code (p:cm_program)`;
  term tail0 =
      `[TVMInst TVMPushOp 8i; TVMInst TVMStoreOp 0i;
        TVMInst TVMCallOp
          (cm_function_pc (p:cm_program) (cm_program_main p));
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMAddOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMHaltOp 0i]:(tvm_inst)list`;
  term tail1 =
      `[TVMInst TVMStoreOp 0i;
        TVMInst TVMCallOp
          (cm_function_pc (p:cm_program) (cm_program_main p));
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMAddOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMHaltOp 0i]:(tvm_inst)list`;
  term tail2 =
      `[TVMInst TVMCallOp
          (cm_function_pc (p:cm_program) (cm_program_main p));
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMAddOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMHaltOp 0i]:(tvm_inst)list`;
  term body = list_mk_conj(TERM_LIST(
      `cm_code_at ${code:(tvm_inst)list} 0i
        (TVMInst TVMPushOp 1048576i :: ${tail0:(tvm_inst)list})`,
      `cm_code_at ${code:(tvm_inst)list} 1i
        (TVMInst TVMPushOp 8i :: ${tail1:(tvm_inst)list})`,
      `cm_code_at ${code:(tvm_inst)list} 2i
        (TVMInst TVMStoreOp 0i :: ${tail2:(tvm_inst)list})`,
      `cm_code_at ${code:(tvm_inst)list} 3i
        ${tail2:(tvm_inst)list}`));
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm at0 = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_emit_prelude_def())),
      spec_rule(`p:cm_program`, cm_model_prelude_at));
  thm suffix_rule = ispecl_rule(TERM_LIST(
      code, `0i:int`, `[TVMInst TVMPushOp 1048576i]:(tvm_inst)list`,
      tail0), cm_code_at_append_right);
  suffix_rule = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("APPEND"))), suffix_rule);
  thm at1 = match_mp_rule(suffix_rule, at0);
  at1 = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("ILENGTH_DEF"))), at1);
  suffix_rule = ispecl_rule(TERM_LIST(
      code, `1i:int`, `[TVMInst TVMPushOp 8i]:(tvm_inst)list`,
      tail1), cm_code_at_append_right);
  suffix_rule = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("APPEND"))), suffix_rule);
  thm at2 = match_mp_rule(suffix_rule, at1);
  at2 = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("ILENGTH_DEF"))), at2);
  suffix_rule = ispecl_rule(TERM_LIST(
      code, `2i:int`, `[TVMInst TVMStoreOp 0i]:(tvm_inst)list`,
      tail2), cm_code_at_append_right);
  suffix_rule = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("APPEND"))), suffix_rule);
  thm at3 = match_mp_rule(suffix_rule, at2);
  at3 = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("ILENGTH_DEF"))), at3);
  ACCEPT_TAC(leaf, conj_rule(at0,
      conj_rule(at1, conj_rule(at2, at3))));
  return gnode_prove(root);
}
PROOF static thm cm_start_prelude_sites =
    cm_prove_start_prelude_sites();

PROOF static thm cm_prove_target_start_prefix(void) {
  term object = `cm_compile_model (p:cm_program)`;
  term initial = `tvm_initial_state ${object:tvm_object} (input:(int)list)`;
  term after =
      `TVMState 3i [] []
        (tower_setw (tvm_mem ${initial:tvm_state}) 8i 1048576i)
        (input:(int)list) []`;
  term body =
      `cm_wf_program (p:cm_program) ==>
       tvm_iter 4 (TVMBoot ${object:tvm_object} (input:(int)list)) ==
         TVMRunTask ${object:tvm_object} ${after:tvm_state}`;
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm object_wf = mp_rule(spec_rule(`p:cm_program`,
      get_cmc_object_wf()), wf);
  thm load = mp_rule(spec_rule(object,
      get_tvm_object_wf_load()), object_wf);
  term code = `cm_model_code (p:cm_program)`;
  term tail0 =
      `[TVMInst TVMPushOp 8i; TVMInst TVMStoreOp 0i;
        TVMInst TVMCallOp
          (cm_function_pc (p:cm_program) (cm_program_main p));
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMAddOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMHaltOp 0i]:(tvm_inst)list`;
  term tail1 =
      `[TVMInst TVMStoreOp 0i;
        TVMInst TVMCallOp
          (cm_function_pc (p:cm_program) (cm_program_main p));
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMAddOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMHaltOp 0i]:(tvm_inst)list`;
  term tail2 =
      `[TVMInst TVMCallOp
          (cm_function_pc (p:cm_program) (cm_program_main p));
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMAddOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMHaltOp 0i]:(tvm_inst)list`;
  thm sites = spec_rule(`p:cm_program`, cm_start_prelude_sites);
  thm at0 = conjunct1_rule(sites);
  thm at1 = conjunct1_rule(conjunct2_rule(sites));
  thm at2 = conjunct1_rule(conjunct2_rule(conjunct2_rule(sites)));
  thm head0 = match_mp_rule(ispecl_rule(TERM_LIST(
      code, `0i:int`, `TVMInst TVMPushOp 1048576i`, tail0),
      cm_code_at_head), at0);
  thm head1 = match_mp_rule(ispecl_rule(TERM_LIST(
      code, `1i:int`, `TVMInst TVMPushOp 8i`, tail1),
      cm_code_at_head), at1);
  thm head2 = match_mp_rule(ispecl_rule(TERM_LIST(
      code, `2i:int`, `TVMInst TVMStoreOp 0i`, tail2),
      cm_code_at_head), at2);
  thm valid0 = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_tvm_target_valid_def())),
      `tvm_target_valid ${code:(tvm_inst)list} 0i`)),
      conj_rule(conjunct1_rule(head0),
        conjunct1_rule(conjunct2_rule(head0))));
  thm valid1 = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_tvm_target_valid_def())),
      `tvm_target_valid ${code:(tvm_inst)list} 1i`)),
      conj_rule(conjunct1_rule(head1),
        conjunct1_rule(conjunct2_rule(head1))));
  thm valid2 = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_tvm_target_valid_def())),
      `tvm_target_valid ${code:(tvm_inst)list} 2i`)),
      conj_rule(conjunct1_rule(head2),
        conjunct1_rule(conjunct2_rule(head2))));
  thm inst0 = conjunct2_rule(conjunct2_rule(head0));
  thm inst1 = conjunct2_rule(conjunct2_rule(head1));
  thm inst2 = conjunct2_rule(conjunct2_rule(head2));
  thm_list rules = THM_LIST(
      conjunct1_rule(get_tvm_iter_def()),
      valid0, valid1, valid2, inst0, inst1, inst2,
      get_tvm_step_def(), get_tvm_inst_step_def(),
      get_tvm_action_task_def(), get_tvm_initial_state_def(),
      get_cm_compile_model_def(),
      get_tvm_object_code_def(), get_tvm_object_entry_def(),
      get_tvm_next_state_def(),
      get_tvm_state_selectors_def(), get_tvm_inst_op_def(),
      get_tvm_inst_imm_def(), get_tower_wrap64_def(),
      get_tower_word_valid_def(),
      get_theorem_by_name("ILENGTH_DEF"),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"), load);
  term iter_index = `0`;
  for (size_t index = 0; index < 4; ++index) {
    thm successor = apply_conversion(
        get_conversion_by_name("NUM_SUC_CONV"),
        mk_comb(`SUC`, iter_index));
    vector_add(&rules, conv_rule(
        rewrite_conv(THM_LIST(successor)),
        spec_rule(iter_index, conjunct2_rule(get_tvm_iter_def()))));
    iter_index = rhs_of(successor);
  }
  gnode reduced = CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv, rules);
  for (size_t stage = 0;
       stage < 12 && IS_NULL(reduced->solved); ++stage) {
    reduced = CONV_WITH_ASMP_TAC(
        reduced, reduce_rewrite_conv, rules);
  }
  return gnode_prove(root);
}
PROOF thm cm_target_start_prefix = cm_prove_target_start_prefix();

PROOF static thm cm_prove_initial_live_address_lower(void) {
  term initial =
      `cm_initial_state (p:cm_program) (input:(int)list)`;
  term body = imp_chain(TERM_LIST(
      `cm_typed_program (p:cm_program)`,
      `cm_live_address ${initial:cm_src_state} (addr:int)`),
      `16i <= (addr:int)`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm typed = assume_rule(`cm_typed_program (p:cm_program)`);
  thm stack = match_mp_rule(
      spec_rule(`p:cm_program`, cm_runtime_stack_halt_initial), typed);
  thm initial_regions_raw = apply_conversion(
      then_conv(rewrite_conv(THM_LIST(get_cm_initial_state_def())),
        reduce_rewrite_conv(get_cm_state_core_defs())),
      `cm_state_regions ${initial:cm_src_state}`);
  thm initial_regions = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(cm_static_regions_def))), initial_regions_raw);
  thm live_exists = conv_rule(rewrite_conv(THM_LIST(
      cm_live_address_def, initial_regions)), assume_rule(
        `cm_live_address ${initial:cm_src_state} (addr:int)`));
  thm live_body = assume_rule(
      `MEM (region:cm_region) (cm_static_regions (p:cm_program)) &&
       cm_region_live region &&
       cm_region_base (cm_static_regions p)
           (cm_region_gen region) + cm_region_lo region <= (addr:int) &&
       addr < cm_region_base (cm_static_regions p)
           (cm_region_gen region) + cm_region_hi region`);
  thm bounds = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `cm_static_regions (p:cm_program)`,
        `[CMACursor CAHaltP 0i 0i 0i]:(cm_acursor)list`,
        `--1i:int`, `1048576i:int`,
        `cm_static_regions (p:cm_program)`,
        `[]:(cm_spill)list`, `[]:(cm_spill_frame)list`,
        `[]:(cm_call_sim_frame)list`, `region:cm_region`),
        cm_runtime_stack_region_bounds),
      stack), conjunct1_rule(live_body)),
      conjunct1_rule(conjunct2_rule(live_body)));
  thm region_lower =
      conjunct1_rule(conjunct2_rule(conjunct2_rule(bounds)));
  thm address_lower =
      conjunct1_rule(conjunct2_rule(conjunct2_rule(live_body)));
  thm result = mp_rule(mp_rule(int_arith_rule(
      `16i <=
         cm_region_base (cm_static_regions (p:cm_program))
           (cm_region_gen (region:cm_region)) +
         cm_region_lo region ==>
       cm_region_base (cm_static_regions p)
           (cm_region_gen region) + cm_region_lo region <= (addr:int) ==>
       16i <= addr`), region_lower), address_lower);
  ACCEPT_TAC(leaf, choose_rule(`region:cm_region`, live_exists, result));
  return gnode_prove(root);
}
PROOF static thm cm_initial_live_address_lower =
    cm_prove_initial_live_address_lower();

PROOF static thm cm_prove_initial_scratch_outside_live(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         cm_typed_program p ==>
         !addr.
           cm_live_address (cm_initial_state p input) addr ==>
           ~(8i <= addr && addr < 16i)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm lower = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`, `addr:int`),
      cm_initial_live_address_lower),
      assume_rule(`cm_typed_program (p:cm_program)`));
  lower = match_mp_rule(lower, assume_rule(
      `cm_live_address
        (cm_initial_state (p:cm_program) (input:(int)list)) (addr:int)`));
  thm impossible = mp_rule(int_arith_rule(
      `16i <= (addr:int) ==>
       8i <= addr && addr < 16i ==>
       F`), lower);
  thm contradiction = match_mp_rule(impossible, assume_rule(
      `8i <= (addr:int) && addr < 16i`));
  ACCEPT_TAC(leaf, contradiction);
  return gnode_prove(root);
}
PROOF static thm cm_initial_scratch_outside_live =
    cm_prove_initial_scratch_outside_live();

PROOF static thm cm_prove_initialized_self(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state).
         cm_initialized_bytes_sim st (cm_state_mem st)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_initialized_bytes_sim_def)));
  return gnode_prove(root);
}
PROOF static thm cm_initialized_self =
    cm_prove_initialized_self();

PROOF static thm cm_prove_initial_initialized_sim(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         cm_initialized_bytes_sim
           (cm_initial_state p input)
           (tvm_mem
             (tvm_initial_state (cm_compile_model p) input))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term source =
      `cm_initial_state (p:cm_program) (input:(int)list)`;
  thm source_mem = apply_conversion(
      then_conv(rewrite_conv(THM_LIST(get_cm_initial_state_def())),
        reduce_rewrite_conv(get_cm_state_core_defs())),
      `cm_state_mem ${source:cm_src_state}`);
  thm target_mem = specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`),
      get_cm_initial_memory_image());
  thm memory_equal = trans_rule(target_mem, sym_rule(source_mem));
  thm predicate_equal = beta_norm(ap_term_rule(
      `\mem:int->int.
        cm_initialized_bytes_sim ${source:cm_src_state} mem`,
      memory_equal));
  thm self = spec_rule(source, cm_initialized_self);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(predicate_equal), self));
  return gnode_prove(root);
}
PROOF static thm cm_initial_initialized_sim =
    cm_prove_initial_initialized_sim();

PROOF static thm cm_prove_initial_untagged(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list) (addr:int).
         ~(cm_state_tagged (cm_initial_state p input) addr)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm impossible = assume_rule(
      `cm_state_tagged
        (cm_initial_state (p:cm_program) (input:(int)list))
        (addr:int)`);
  impossible = conv_rule(
      rewrite_conv(THM_LIST(get_cm_initial_state_def())), impossible);
  impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_state_make_def(), get_cm_state_tagged_def())), impossible);
  CONTR_TAC(leaf, impossible);
  return gnode_prove(root);
}
PROOF static thm cm_initial_untagged =
    cm_prove_initial_untagged();

PROOF static thm cm_prove_initial_provenance_sim(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         cm_stored_provenance_sim
           (cm_initial_state p input)
           (tvm_mem
             (tvm_initial_state (cm_compile_model p) input))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_stored_provenance_sim_def)));
  gnode with_addr = GEN_TAC(opened, "addr");
  gnode consequence = DISCH_TAC(with_addr, "Hlive_tagged");
  thm tagged = conjunct1_rule(assume_rule(
      `cm_state_tagged
         (cm_initial_state (p:cm_program) (input:(int)list))
         (addr:int) &&
       cm_live_address
         (cm_initial_state (p:cm_program) (input:(int)list))
         addr`));
  thm untagged = specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`, `addr:int`),
      cm_initial_untagged);
  CONTR_TAC(consequence, not_elim_rule(untagged, tagged));
  return gnode_prove(root);
}
PROOF static thm cm_initial_provenance_sim =
    cm_prove_initial_provenance_sim();

PROOF static thm cm_prove_initial_machine_sim(void) {
  term object = `cm_compile_model (p:cm_program)`;
  term initial_target =
      `tvm_initial_state ${object:tvm_object} (input:(int)list)`;
  term memory =
      `tower_setw (tvm_mem ${initial_target:tvm_state}) 8i 1048576i`;
  term after =
      `TVMState 3i [] [] ${memory:int->int} (input:(int)list) []`;
  term source =
      `cm_initial_state (p:cm_program) (input:(int)list)`;
  term body = mk_imp(`cm_typed_program (p:cm_program)`,
      `cm_machine_state_sim (p:cm_program) ${source:cm_src_state}
        ${after:tvm_state} []
        [CMSpillFrame (--1i) 1048576i []] [] []`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm typed = assume_rule(`cm_typed_program (p:cm_program)`);
  thm outside = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`),
      cm_initial_scratch_outside_live), typed);
  thm signed_word = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_tower_signed64_def())),
      `tower_signed64 1048576i`));
  thm initialized = specl_rule(TERM_LIST(
      source, `tvm_mem ${initial_target:tvm_state}`,
      `8i:int`, `1048576i:int`),
      get_cm_initialized_scratch_store_sim());
  initialized = match_mp_rule(initialized,
      specl_rule(TERM_LIST(`p:cm_program`, `input:(int)list`),
        cm_initial_initialized_sim));
  initialized = match_mp_rule(initialized, signed_word);
  initialized = conv_rule(reduce_rewrite_conv(THM_LIST()), initialized);
  initialized = match_mp_rule(initialized, outside);
  thm provenance = specl_rule(TERM_LIST(
      source, `tvm_mem ${initial_target:tvm_state}`,
      `8i:int`, `1048576i:int`),
      get_cm_provenance_scratch_store_sim());
  provenance = match_mp_rule(provenance,
      specl_rule(TERM_LIST(`p:cm_program`, `input:(int)list`),
        cm_initial_provenance_sim));
  provenance = match_mp_rule(provenance, signed_word);
  provenance = match_mp_rule(provenance,
      specl_rule(TERM_LIST(`p:cm_program`, `input:(int)list`),
        cm_tagged_span_initial));
  provenance = conv_rule(reduce_rewrite_conv(THM_LIST()), provenance);
  provenance = match_mp_rule(provenance, outside);
  thm fp_word = specl_rule(TERM_LIST(
      `tvm_mem ${initial_target:tvm_state}`, `8i:int`, `1048576i:int`),
      get_tower_getw_setw());
  thm wrap_fixed = mp_rule(
      spec_rule(`1048576i`, get_tower_wrap64_fixed()), signed_word);
  fp_word = conv_rule(rewrite_conv(THM_LIST(wrap_fixed)), fp_word);
  thm source_fp = apply_conversion(
      rewrite_conv(THM_LIST(get_cm_initial_state_def())),
      `cm_state_fp ${source:cm_src_state}`);
  source_fp = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_state_make_def(), get_cm_state_fp_def())), source_fp);
  fp_word = trans_rule(fp_word, sym_rule(source_fp));
  thm_list simple_rules = THM_LIST(
      cm_call_frames_sim_def, cm_spill_frames_sim_def,
      cm_spill_list_sim_def, cm_spill_frame_fid_def,
      cm_spill_frame_fp_def, cm_spill_frame_spills_def,
      cm_operand_suffix_sim_def, cm_encode_values_def,
      get_cm_initial_state_def(), get_cm_state_make_def(),
      get_cm_state_input_def(), get_cm_state_output_def(),
      get_tvm_state_selectors_def());
  thm calls = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(simple_rules),
      `cm_call_frames_sim ${memory:int->int} [] []`));
  thm spills = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(simple_rules),
      `cm_spill_frames_sim (p:cm_program) ${source:cm_src_state}
        ${memory:int->int} [CMSpillFrame (--1i) 1048576i []]`));
  thm input_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(simple_rules),
      `tvm_input ${after:tvm_state} == cm_state_input ${source:cm_src_state}`));
  thm output_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(simple_rules),
      `tvm_output ${after:tvm_state} ==
       cm_state_output ${source:cm_src_state}`));
  thm operands = eqt_elim_rule(apply_conversion(
      then_conv(reduce_rewrite_conv(simple_rules),
        reduce_rewrite_conv(THM_LIST(get_theorem_by_name("APPEND")))),
      `cm_operand_suffix_sim ${source:cm_src_state} [] []
        (tvm_stack ${after:tvm_state})`));
  thm combined = conj_rule(initialized,
      conj_rule(provenance,
      conj_rule(fp_word,
      conj_rule(calls,
      conj_rule(spills,
      conj_rule(input_equal,
      conj_rule(output_equal, operands)))))));
  combined = conv_rule(rewrite_conv(THM_LIST(
      get_tvm_state_selectors_def())), combined);
  thm target_view = apply_conversion(rewrite_conv(THM_LIST(
      cm_machine_state_sim_def, get_tvm_state_selectors_def())),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), combined));
  return gnode_prove(root);
}
PROOF static thm cm_initial_machine_sim =
    cm_prove_initial_machine_sim();

PROOF static thm cm_prove_initial_running_target_sim(void) {
  term object = `cm_compile_model (p:cm_program)`;
  term initial_target =
      `tvm_initial_state ${object:tvm_object} (input:(int)list)`;
  term memory =
      `tower_setw (tvm_mem ${initial_target:tvm_state}) 8i 1048576i`;
  term after =
      `TVMState 3i [] [] ${memory:int->int} (input:(int)list) []`;
  term source =
      `cm_initial_state (p:cm_program) (input:(int)list)`;
  term call_ann =
      `CMAnnotation 3i 0i 0i 0i
        [CMACursor CAHaltP 0i 0i 0i] [] [] []`;
  term target =
      `tvm_iter 4 (TVMBoot ${object:tvm_object} (input:(int)list))`;
  term body = mk_imp(`cm_wf_program (p:cm_program)`,
      `cm_running_target_sim (p:cm_program) (--1i)
        ${source:cm_src_state} [] ${call_ann:cm_annotation}
        ${target:tvm_task}`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm wf_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_wf_program_def(), get_cm_codegen_admissible_def())), wf);
  thm typed = cm_start_pick(
      wf_opened, `cm_typed_program (p:cm_program)`);
  thm prefix = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`),
      cm_target_start_prefix), wf);
  thm machine = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`),
      cm_initial_machine_sim), typed);
  term desired_machine =
      `cm_machine_state_sim (p:cm_program) ${source:cm_src_state}
        ${after:tvm_state} []
        (cm_active_spill_frames (--1i) ${source:cm_src_state}
          ${call_ann:cm_annotation}) [] []`;
  thm source_fp = apply_conversion(
      rewrite_conv(THM_LIST(get_cm_initial_state_def())),
      `cm_state_fp ${source:cm_src_state}`);
  source_fp = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_state_make_def(), get_cm_state_fp_def())), source_fp);
  thm machine_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      cm_active_spill_frames_def, cm_ann_spills_def,
      cm_ann_saved_def, source_fp)), desired_machine);
  thm desired_machine_proof =
      eq_mp_rule(sym_rule(machine_view), machine);
  thm pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_tvm_state_selectors_def(), cm_ann_pc_def)),
      `tvm_pc ${after:tvm_state} == cm_ann_pc ${call_ann:cm_annotation}`));
  term exists_body =
      `?vm:tvm_state.
         ${target:tvm_task} ==
           TVMRunTask ${object:tvm_object} vm &&
         tvm_pc vm == cm_ann_pc ${call_ann:cm_annotation} &&
         cm_machine_state_sim (p:cm_program) ${source:cm_src_state}
           vm (cm_ann_calls ${call_ann:cm_annotation})
           (cm_active_spill_frames (--1i) ${source:cm_src_state}
             ${call_ann:cm_annotation}) [] []`;
  dest_exists_results exists_parts = dest_exists(exists_body);
  term instantiated_body =
      subst_one(after, exists_parts.v, exists_parts.tm);
  thm_list witness_rules = THM_LIST(
      get_tvm_state_selectors_def(), cm_ann_pc_def,
      cm_ann_calls_def, cm_active_spill_frames_def,
      cm_ann_spills_def, cm_ann_saved_def, source_fp);
  thm body_reduction = apply_conversion(
      reduce_rewrite_conv(witness_rules), instantiated_body);
  thm normalized_body = conv_rule(
      reduce_rewrite_conv(witness_rules),
      conj_rule(prefix, conj_rule(pc, desired_machine_proof)));
  thm adjusted_body =
      eq_mp_rule(sym_rule(body_reduction), normalized_body);
  thm witness = exists_rule(exists_body, after, adjusted_body);
  thm running_view = apply_conversion(
      rewrite_conv(THM_LIST(cm_running_target_sim_def)),
      `cm_running_target_sim (p:cm_program) (--1i)
        ${source:cm_src_state} [] ${call_ann:cm_annotation}
        ${target:tvm_task}`);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(running_view), witness));
  return gnode_prove(root);
}
PROOF static thm cm_initial_running_target_sim =
    cm_prove_initial_running_target_sim();

PROOF static thm cm_prove_initial_call_target_ready(void) {
  term initial =
      `cm_initial_state (p:cm_program) (input:(int)list)`;
  term body = imp_chain(TERM_LIST(
      `cm_wf_program (p:cm_program)`,
      `cm_call_ok p (cm_program_main p) []
        ${initial:cm_src_state}`),
      `cm_call_target_ready p (--1i) (cm_program_main p) []
        ${initial:cm_src_state} CMIntTy 4i 0i 0i 0i
        [CMACursor CAHaltP 0i 0i 0i] [] [] []`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm wf_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_wf_program_def(), get_cm_codegen_admissible_def())), wf);
  thm typed = cm_start_pick(
      wf_opened, `cm_typed_program (p:cm_program)`);
  thm state_generation = specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`),
      cm_state_generation_initial);
  thm depth = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_call_depth_def(), get_cm_is_call_frame_def(),
        cm_cursor_frames_def, cm_cursor_phase_def,
        cm_phase_frame_def, get_theorem_by_name("ILENGTH_DEF"))),
      `cm_call_depth
        (cm_cursor_frames
          [CMACursor CAHaltP 0i 0i 0i]) < 65536i`));
  thm initial_fp = apply_conversion(
      rewrite_conv(THM_LIST(get_cm_initial_state_def())),
      `cm_state_fp ${initial:cm_src_state}`);
  initial_fp = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_state_make_def(), get_cm_state_fp_def())), initial_fp);
  thm initial_nextgen = apply_conversion(
      rewrite_conv(THM_LIST(get_cm_initial_state_def())),
      `cm_state_nextgen ${initial:cm_src_state}`);
  initial_nextgen = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_state_make_def(), get_cm_state_nextgen_def())),
      initial_nextgen);
  thm initial_regions_raw = apply_conversion(
      rewrite_conv(THM_LIST(get_cm_initial_state_def())),
      `cm_state_regions ${initial:cm_src_state}`);
  initial_regions_raw = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_state_make_def(), get_cm_state_regions_def())),
      initial_regions_raw);
  thm initial_regions = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(cm_static_regions_def))), initial_regions_raw);
  thm before = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(initial_regions), sym_rule(initial_nextgen))),
      spec_rule(`p:cm_program`, cm_static_regions_before_dynamic));
  thm stack = match_mp_rule(
      spec_rule(`p:cm_program`, cm_runtime_stack_halt_initial), typed);
  stack = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(initial_regions), sym_rule(initial_fp))), stack);
  thm call_ready = specl_rule(TERM_LIST(
      `p:cm_program`, `--1i:int`, `cm_program_main (p:cm_program)`,
      `[]:(cm_value)list`, initial, `CMIntTy`, `4i:int`, `0i:int`,
      `0i:int`, `0i:int`,
      `[CMACursor CAHaltP 0i 0i 0i]:(cm_acursor)list`,
      `[]:(cm_spill)list`, `[]:(cm_spill_frame)list`,
      `[]:(cm_call_sim_frame)list`),
      get_cm_target_call_ready());
  call_ready = match_mp_rule(call_ready, wf);
  call_ready = match_mp_rule(call_ready, state_generation);
  call_ready = match_mp_rule(call_ready, assume_rule(
      `cm_call_ok (p:cm_program) (cm_program_main p) []
        ${initial:cm_src_state}`));
  call_ready = match_mp_rule(call_ready, depth);
  call_ready = match_mp_rule(call_ready, before);
  call_ready = match_mp_rule(call_ready, stack);
  ACCEPT_TAC(leaf, call_ready);
  return gnode_prove(root);
}
PROOF static thm cm_initial_call_target_ready =
    cm_prove_initial_call_target_ready();

PROOF static thm cm_prove_start_code_steps_append(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:(tvm_inst)list) (right:(tvm_inst)list).
         cm_code_steps (left ++ right) ==
         cm_code_steps left + cm_code_steps right`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm left_nonnegative = ispec_rule(
      `left:(tvm_inst)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm right_nonnegative = ispec_rule(
      `right:(tvm_inst)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm count_add = match_mp_rule(specl_rule(TERM_LIST(
      `ilength (left:(tvm_inst)list)`,
      `ilength (right:(tvm_inst)list)`),
      get_theorem_by_name("NUM_OF_INT_ADD")),
      conj_rule(left_nonnegative, right_nonnegative));
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_code_steps_def, get_theorem_by_name("ILENGTH_APPEND"),
      count_add)));
  return gnode_prove(root);
}
PROOF static thm cm_start_code_steps_append =
    cm_prove_start_code_steps_append();

PROOF static thm cm_prove_start_entry_steps(void) {
  term params =
      `cm_function_params
        (inth (cm_program_main (p:cm_program))
          (cm_program_functions p))`;
  term param_steps =
      `cm_code_steps
        (cm_emit_param_stores (p:cm_program)
          (cm_program_main p) 0i ${params:(cm_slot_d)list})`;
  term equation =
      `cm_entry_steps (p:cm_program) ==
       4 + (1 + (6 + (6 + (2 + ${param_steps:num}))))`;
  thm view = apply_conversion(
      then_conv(
        then_conv(
          rewrite_conv(THM_LIST(
            cm_entry_steps_def, get_cm_emit_prologue_def(),
            cm_start_code_steps_append)),
          reduce_rewrite_conv(THM_LIST(
            cm_code_steps_def,
            get_theorem_by_name("ILENGTH_APPEND"),
            get_theorem_by_name("ILENGTH_DEF")))),
        rewrite_conv(THM_LIST(
          spec_rule(`14:num`,
            get_theorem_by_name("NUM_OF_INT_OF_NUM"))))),
      equation);
  struct dest_iff_results sides = dest_iff(concl(view));
  thm result = eq_mp_rule(sym_rule(view), arith_rule(sides.tm2));
  return gen_rule(`p:cm_program`, result);
}
PROOF static thm cm_start_entry_steps =
    cm_prove_start_entry_steps();

PROOF static thm cm_prove_initial_call_complete(void) {
  term initial =
      `cm_initial_state (p:cm_program) (input:(int)list)`;
  term main_fid = `cm_program_main (p:cm_program)`;
  term call_ann =
      `CMAnnotation 3i 0i 0i 0i
        [CMACursor CAHaltP 0i 0i 0i] [] [] []`;
  term entered =
      `cm_ann_enter_call (p:cm_program) (--1i) ${main_fid:int}
        ${initial:cm_src_state} CMIntTy 4i 0i 0i 0i
        [CMACursor CAHaltP 0i 0i 0i] [] [] []`;
  term target =
      `tvm_iter 4
        (TVMBoot (cm_compile_model (p:cm_program)) (input:(int)list))`;
  term call_rest =
      `[TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMAddOp 0i;
        TVMInst TVMPushOp 256i; TVMInst TVMModOp 0i;
        TVMInst TVMHaltOp 0i]:(tvm_inst)list`;
  term params =
      `cm_function_params
        (inth ${main_fid:int}
          (cm_program_functions (p:cm_program)))`;
  term frame_base =
      `cm_state_fp ${initial:cm_src_state} -
        cm_frame_size (cm_program_structs (p:cm_program))
          (inth ${main_fid:int} (cm_program_functions p))`;
  term active =
      `cm_active_spill_frames (--1i) ${initial:cm_src_state}
        ${call_ann:cm_annotation}`;
  term active_explicit =
      `[CMSpillFrame (--1i) (cm_state_fp ${initial:cm_src_state}) []]
        :(cm_spill_frame)list`;
  term pending =
      `cm_call_pending_base (p:cm_program) ${main_fid:int}
        ${initial:cm_src_state}`;
  term body = imp_chain(TERM_LIST(
      `cm_wf_program (p:cm_program)`,
      `cm_call_ok p ${main_fid:int} [] ${initial:cm_src_state}`),
      `cm_running_target_sim p ${main_fid:int}
        (cm_enter_call p ${main_fid:int} [] ${initial:cm_src_state})
        [] ${entered:cm_annotation}
        (tvm_iter
          (cm_code_steps
            (cm_emit_param_stores p ${main_fid:int} 0i
              ${params:(cm_slot_d)list}))
          (tvm_iter 2
            (tvm_iter 6
              (tvm_iter 6
                (tvm_iter 1 ${target:tvm_task})))))`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm call_ok = assume_rule(
      `cm_call_ok (p:cm_program) ${main_fid:int} []
        ${initial:cm_src_state}`);
  thm ready = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(`p:cm_program`, `input:(int)list`),
        cm_initial_call_target_ready), wf), call_ok);
  thm ready_opened = conv_rule(rewrite_conv(THM_LIST(
      cm_call_target_ready_def)), ready);
  thm call_opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_call_ok_def())), call_ok);
  thm callee_bounds = cm_start_pick(call_opened,
      `0i <= ${main_fid:int} &&
       ${main_fid:int} < ilength (cm_program_functions (p:cm_program))`);
  thm arity = cm_start_pick(call_opened,
      `ilength ([]:(cm_value)list) ==
       ilength ${params:(cm_slot_d)list}`);
  thm state_generation = specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`),
      cm_state_generation_initial);
  thm state_opened = conv_rule(rewrite_conv(THM_LIST(
      cm_state_generation_below_def)), state_generation);
  thm state_tags = match_mp_rule(specl_rule(TERM_LIST(
      initial, `cm_state_nextgen ${initial:cm_src_state}`),
      cm_state_tags_generation_from_all),
      conjunct2_rule(conjunct2_rule(state_opened)));
  thm empty_values = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_values_generation_below_def)),
      `cm_values_generation_below
        (cm_state_nextgen ${initial:cm_src_state})
        ([]:(cm_value)list)`));
  thm active_generation = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_active_spill_frames_def, cm_ann_spills_def,
        cm_ann_saved_def, cm_spill_frames_generation_below_def,
        cm_spill_frame_spills_def, cm_spills_generation_below_def)),
      `cm_spill_frames_generation_below
        (cm_state_nextgen ${initial:cm_src_state})
        ${active:(cm_spill_frame)list}`));
  thm tagged = specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`), cm_tagged_span_initial);
  thm initial_nextgen = apply_conversion(
      rewrite_conv(THM_LIST(get_cm_initial_state_def())),
      `cm_state_nextgen ${initial:cm_src_state}`);
  initial_nextgen = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_state_make_def(), get_cm_state_nextgen_def())),
      initial_nextgen);
  thm initial_regions_raw = apply_conversion(
      rewrite_conv(THM_LIST(get_cm_initial_state_def())),
      `cm_state_regions ${initial:cm_src_state}`);
  initial_regions_raw = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_state_make_def(), get_cm_state_regions_def())),
      initial_regions_raw);
  thm initial_regions = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(cm_static_regions_def))), initial_regions_raw);
  thm before = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(initial_regions), sym_rule(initial_nextgen))),
      spec_rule(`p:cm_program`, cm_static_regions_before_dynamic));
  thm active_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_active_spill_frames_def, cm_ann_spills_def,
        cm_ann_saved_def)),
      `${active:(cm_spill_frame)list} ==
       ${active_explicit:(cm_spill_frame)list}`));
  thm sites = spec_rule(`p:cm_program`, cm_start_prelude_sites);
  thm call_site =
      conjunct2_rule(conjunct2_rule(conjunct2_rule(sites)));
  thm running = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`),
      cm_initial_running_target_sim), wf);
  thm eight_sum = apply_conversion(
      reduce_rewrite_conv(THM_LIST()), `8i + 8i`);
  thm three_one = apply_conversion(
      reduce_rewrite_conv(THM_LIST()), `3i + 1i`);
  thm result = specl_rule(TERM_LIST(
      call_rest, `--1i:int`, call_ann, `[]:(cm_value)list`,
      initial, entered, main_fid, `p:cm_program`, target),
      get_cm_target_call_complete());
  result = conv_rule(rewrite_conv(THM_LIST(
      cm_ann_pc_def, cm_ann_calls_def, eight_sum, three_one,
      get_theorem_by_name("REVERSE"))), result);
  result = match_mp_rule(result, call_site);
  result = match_mp_rule(result, running);
  result = match_mp_rule(result, callee_bounds);
  term_list first_ready = TERM_LIST(
      `tvm_target_valid (cm_model_code (p:cm_program))
        (cm_function_pc p ${main_fid:int})`,
      `cm_function_wf (p:cm_program)
        (inth ${main_fid:int} (cm_program_functions p))`,
      `cm_frame_segment (p:cm_program) ${main_fid:int}
        ${frame_base:int} (cm_state_fp ${initial:cm_src_state})`);
  for (size_t index = 0; index < vector_size(first_ready); ++index) {
    result = match_mp_rule(result,
        find_conjunct_rule(ready_opened, first_ready[index]));
  }
  result = match_mp_rule(result, before);
  term_list capacity_ready = TERM_LIST(
      `0i <= cm_state_nextgen ${initial:cm_src_state}`,
      `ilength ([]:(cm_call_sim_frame)list) < 65536i`,
      `ilength ([]:(cm_value)list) < 65534i`);
  for (size_t index = 0; index < vector_size(capacity_ready); ++index) {
    result = match_mp_rule(result,
        find_conjunct_rule(ready_opened, capacity_ready[index]));
  }
  result = match_mp_rule(result, state_tags);
  result = match_mp_rule(result, empty_values);
  result = match_mp_rule(result, active_generation);
  result = match_mp_rule(result, tagged);
  term_list memory_ready = TERM_LIST(
      `!addr:int.
         cm_live_address ${initial:cm_src_state} addr ==>
         ~(${frame_base:int} <= addr &&
           addr < ${frame_base:int} + 8i)`,
      `!addr:int.
         cm_live_address ${initial:cm_src_state} addr ==>
         ~(8i <= addr && addr < 16i)`,
      `cm_range_disjoint ${frame_base:int} 8i 8i 8i`,
      `cm_range_disjoint 8i 8i ${frame_base:int} 8i`,
      `cm_call_frames_store_safe CMIntTy ${frame_base:int}
        ([]:(cm_call_sim_frame)list)`,
      `cm_spill_frames_store_safe (p:cm_program) CMIntTy
        ${frame_base:int} ${active_explicit:(cm_spill_frame)list}`,
      `cm_call_frames_store_safe CMIntTy 8i
        ([]:(cm_call_sim_frame)list)`,
      `cm_spill_frames_store_safe (p:cm_program) CMIntTy 8i
        ${active_explicit:(cm_spill_frame)list}`,
      `tower_signed64 (cm_state_fp ${initial:cm_src_state})`,
      `tower_signed64
        (cm_frame_size (cm_program_structs (p:cm_program))
          (inth ${main_fid:int} (cm_program_functions p)))`,
      `tower_signed64 ${frame_base:int}`,
      `tower_word_valid ${frame_base:int}`);
  for (size_t index = 0; index < vector_size(memory_ready); ++index) {
    thm fact = find_conjunct_rule(ready_opened, memory_ready[index]);
    if (index == 5 || index == 7) {
      fact = conv_rule(rewrite_conv(THM_LIST(sym_rule(active_equal))),
          fact);
    }
    result = match_mp_rule(result, fact);
  }
  thm pending_layout = find_conjunct_rule(ready_opened,
      `cm_runtime_memory_layout (p:cm_program)
        ${pending:cm_src_state}
        (cm_ann_calls ${entered:cm_annotation})
        (cm_active_spill_frames ${main_fid:int}
          ${pending:cm_src_state} ${entered:cm_annotation})`);
  result = match_mp_rule(result, pending_layout);
  thm entered_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_enter_call_def, cm_ann_pc_def)),
      `cm_ann_pc ${entered:cm_annotation} ==
       cm_call_body_pc (p:cm_program) ${main_fid:int}`));
  result = match_mp_rule(result, entered_pc);
  thm entered_calls = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_enter_call_def, cm_ann_calls_def, three_one)),
      `cm_ann_calls ${entered:cm_annotation} ==
       CMCallSimFrame ${frame_base:int}
         (cm_state_fp ${initial:cm_src_state}) 4i ::
       ([]:(cm_call_sim_frame)list)`));
  result = match_mp_rule(result, entered_calls);
  thm entered_active = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_active_spill_frames_def, cm_ann_enter_call_def,
        cm_ann_spills_def, cm_ann_saved_def,
        get_cm_call_pending_base_def(), get_cm_state_make_def(),
        get_cm_state_fp_def())),
      `cm_active_spill_frames ${main_fid:int}
          ${pending:cm_src_state} ${entered:cm_annotation} ==
       CMSpillFrame ${main_fid:int} ${frame_base:int} [] ::
         ${active:(cm_spill_frame)list}`));
  result = match_mp_rule(result, entered_active);
  result = match_mp_rule(result, arity);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF static thm cm_initial_call_complete =
    cm_prove_initial_call_complete();

PROOF static thm cm_prove_target_start_step(void) {
  term task =
      `CMStartTask (p:cm_program) (input:(int)list)`;
  term update =
      `cm_annotation_step ${task:cm_task} (ann:cm_annotation)`;
  term body = imp_chain(TERM_LIST(
      `cm_wf_program (p:cm_program)`,
      `cm_runtime_step_ready p ${task:cm_task} (ann:cm_annotation)`,
      `cm_task_target_sim p ${task:cm_task}
        (target:tvm_task) (ann:cm_annotation)`),
      `cm_task_target_sim p (cm_step ${task:cm_task})
        (tvm_iter (cm_update_steps ${update:cm_aupdate})
          (target:tvm_task))
        (cm_update_annotation ${update:cm_aupdate})`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm readiness = assume_rule(
      `cm_runtime_step_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm readiness_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_runtime_step_ready_def, cm_task_layout_ready_def)), readiness);
  thm call_ok = find_conjunct_rule(readiness_opened,
      `cm_call_ok (p:cm_program) (cm_program_main p) []
        (cm_initial_state p (input:(int)list))`);
  thm ann_equal = find_conjunct_rule(readiness_opened,
      `(ann:cm_annotation) == cm_initial_annotation`);
  thm old_sim = assume_rule(
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) (ann:cm_annotation)`);
  thm old_sim_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), old_sim);
  thm target_equal = find_conjunct_rule(old_sim_opened,
      `(target:tvm_task) ==
       TVMBoot (cm_compile_model (p:cm_program)) (input:(int)list)`);
  thm result = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(`p:cm_program`, `input:(int)list`),
        cm_initial_call_complete), wf), call_ok);
  thm step_count = spec_rule(`p:cm_program`, cm_start_entry_steps);
  result = conv_rule(reduce_rewrite_conv(THM_LIST(
      gsym_rule(get_cm_tvm_iter_add()),
      get_theorem_by_name("ADD_ASSOC"), gsym_rule(step_count))), result);
  thm depth = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_call_depth_def(), get_cm_is_call_frame_def(),
        get_theorem_by_name("ILENGTH_DEF"))),
      `cm_call_depth ([CMHaltK]:(cm_frame)list) < 65536i`));
  thm_list finish_rules = THM_LIST(
      get_cm_step_def(), get_cm_begin_call_def(), call_ok, depth,
      cm_annotation_step_def, cm_initial_annotation_def,
      cm_update_steps_def, cm_update_annotation_def,
      cm_task_target_sim_def);
  conv finish = then_conv(
      rewrite_conv(THM_LIST(ann_equal, target_equal)),
      then_conv(reduce_rewrite_conv(finish_rules),
        reduce_rewrite_conv(finish_rules)));
  thm target_view = apply_conversion(finish, goal_ccl(leaf->g));
  thm normalized = conv_rule(finish, result);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}
PROOF thm cm_target_start_step = cm_prove_target_start_step();
PROOF thm get_cm_target_start_step(void) {
  return cm_target_start_step;
}

PROOF static int cmc_preservation_target_start_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_start_axioms_before,
      "cmc_preservation_target_start introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_start_prefix)) == 0,
      "cm_target_start_prefix has hypotheses");
  ENSURE_COND(vector_size(hyp(cm_initial_running_target_sim)) == 0,
      "cm_initial_running_target_sim has hypotheses");
  ENSURE_COND(vector_size(hyp(cm_initial_call_target_ready)) == 0,
      "cm_initial_call_target_ready has hypotheses");
  ENSURE_COND(vector_size(hyp(cm_initial_call_complete)) == 0,
      "cm_initial_call_complete has hypotheses");
  ENSURE_COND(vector_size(hyp(cm_target_start_step)) == 0,
      "cm_target_start_step has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_start_checks =
    cmc_preservation_target_start_final_checks();
