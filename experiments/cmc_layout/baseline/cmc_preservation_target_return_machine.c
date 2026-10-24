#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_return_machine.h"
#include "cmc_preservation_machine_ops.h"
#include "cmc_preservation_target_restore.h"
#include "cmc_preservation_machine_store.h"
#include "cmc_preservation_invariant_step.h"
#include "cmc_preservation_tagged_restore_list.h"
#include "cmc_preservation_call_transport.h"
#include "cmc_preservation_call_value.h"

#require "cmc_preservation_target_machine.c"
#require "cmc_preservation_target_restore.c"
#require "cmc_preservation_machine_store.c"

PROOF static size_t _cmc_preservation_target_return_machine_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_restore_call_initialized_transport(void) {
  term body = imp_chain(TERM_LIST(
      `cm_region_prefix_safe (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (oldregions:(cm_region)list)`,
      `cm_initialized_bytes_sim (st:cm_src_state) (mem:int->int)`),
      `cm_initialized_bytes_sim
        (cm_restore_call (st:cm_src_state)
          (oldenv:int->int->cm_value) (oldfp:int)
          (oldregions:(cm_region)list))
        (mem:int->int)`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm raw = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `oldenv:int->int->cm_value`, `oldregions:(cm_region)list`,
      `mem:int->int`), get_cm_restore_initialized_transport()),
      assume_rule(
        `cm_region_prefix_safe (p:cm_program)
          (cm_state_regions (st:cm_src_state)) (fid:int)
          (cm_state_fp st) (cm_state_regions st)
          (oldregions:(cm_region)list)`)),
      assume_rule(
        `cm_initialized_bytes_sim (st:cm_src_state) (mem:int->int)`));
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_restore_scope_def());
  vector_add(&rules, get_cm_restore_call_def());
  vector_add(&rules, cm_initialized_bytes_sim_def);
  vector_add(&rules, cm_live_address_def);
  thm normalized = conv_rule(reduce_rewrite_conv(rules), raw);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}
PROOF static thm cm_restore_call_initialized_transport =
    cm_prove_restore_call_initialized_transport();

PROOF static thm cm_prove_restore_call_provenance_transport(void) {
  term active = `cm_state_regions (st:cm_src_state)`;
  term restored =
      `cm_restore_call (st:cm_src_state)
        (oldenv:int->int->cm_value) (oldfp:int)
        (oldregions:(cm_region)list)`;
  term body = imp_chain(TERM_LIST(
      `cm_region_prefix_safe (p:cm_program) ${active:(cm_region)list}
        (fid:int) (cm_state_fp st) ${active:(cm_region)list}
        (oldregions:(cm_region)list)`,
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`,
      `cm_stored_provenance_sim (st:cm_src_state) (mem:int->int)`),
      `cm_stored_provenance_sim ${restored:cm_src_state}
        (mem:int->int)`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm prefix = assume_rule(
      `cm_region_prefix_safe (p:cm_program) ${active:(cm_region)list}
        (fid:int) (cm_state_fp st) ${active:(cm_region)list}
        (oldregions:(cm_region)list)`);
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
  vector_add(&state_rules, get_cm_restore_call_def());
  thm new_tagged = conv_rule(reduce_rewrite_conv(state_rules),
      conjunct1_rule(new_parts));
  thm old_tagged = mp_rule(specl_rule(TERM_LIST(active, active,
      `oldregions:(cm_region)list`, `cm_state_tagged (st:cm_src_state)`,
      `addr:int`), cm_restore_tagged_source), new_tagged);
  thm call_live = conjunct2_rule(new_parts);
  thm call_live_normalized = conv_rule(then_conv(
      rewrite_conv(THM_LIST(cm_live_address_def)),
      reduce_rewrite_conv(state_rules)), call_live);
  term scope_live =
      `cm_live_address
        (cm_restore_scope (st:cm_src_state)
          (oldenv:int->int->cm_value) (oldregions:(cm_region)list))
        (addr:int)`;
  thm_list scope_rules = get_cm_state_core_defs();
  vector_add(&scope_rules, get_cm_restore_scope_def());
  thm scope_live_view = apply_conversion(then_conv(
      rewrite_conv(THM_LIST(cm_live_address_def)),
      reduce_rewrite_conv(scope_rules)), scope_live);
  thm scope_live_fact =
      eq_mp_rule(sym_rule(scope_live_view), call_live_normalized);
  thm old_live = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `oldenv:int->int->cm_value`, `oldregions:(cm_region)list`,
      `addr:int`), get_cm_restore_scope_live_source()), prefix);
  old_live = match_mp_rule(old_live, scope_live_fact);
  thm old_point = match_mp_rule(spec_rule(`addr:int`, old_sim),
      conj_rule(old_tagged, old_live));
  thm new_init = specl_rule(TERM_LIST(active, `p:cm_program`, active,
      `fid:int`, `cm_state_fp (st:cm_src_state)`,
      `oldregions:(cm_region)list`,
      `cm_state_init (st:cm_src_state)`,
      `cm_state_tagged (st:cm_src_state)`, `addr:int`),
      get_cm_restore_tagged_init_lockstep());
  new_init = match_mp_rule(new_init, prefix);
  new_init = match_mp_rule(new_init, new_tagged);
  new_init = match_mp_rule(new_init, conjunct1_rule(old_point));
  thm bases = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, active, `fid:int`, `cm_state_fp (st:cm_src_state)`,
      active, `oldregions:(cm_region)list`),
      cm_restore_regions_bases), prefix);
  thm below_bases = match_mp_rule(specl_rule(TERM_LIST(
      `cm_restore_regions ${active:(cm_region)list}
        (oldregions:(cm_region)list)`,
      active, `cm_state_nextgen (st:cm_src_state)`),
      get_cm_region_bases_equal_below()), bases);
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
PROOF static thm cm_restore_call_provenance_transport =
    cm_prove_restore_call_provenance_transport();
PROOF static thm cm_prove_restore_call_bases_below(void) {
  term restored =
      `cm_restore_call (st:cm_src_state)
        (oldenv:int->int->cm_value) (oldfp:int)
        (oldregions:(cm_region)list)`;
  term body = mk_imp(
      `cm_region_prefix_safe (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (oldregions:(cm_region)list)`,
      `cm_region_bases_below_equal
        (cm_state_regions ${restored:cm_src_state})
        (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm prefix = assume_rule(
      `cm_region_prefix_safe (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (oldregions:(cm_region)list)`);
  thm bases = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
      `fid:int`, `cm_state_fp (st:cm_src_state)`,
      `cm_state_regions (st:cm_src_state)`,
      `oldregions:(cm_region)list`),
      cm_restore_regions_bases), prefix);
  thm below = match_mp_rule(specl_rule(TERM_LIST(
      `cm_restore_regions (cm_state_regions (st:cm_src_state))
        (oldregions:(cm_region)list)`,
      `cm_state_regions (st:cm_src_state)`,
      `cm_state_nextgen (st:cm_src_state)`),
      get_cm_region_bases_equal_below()), bases);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_restore_call_def());
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), below));
  return gnode_prove(root);
}
PROOF static thm cm_restore_call_bases_below =
    cm_prove_restore_call_bases_below();
PROOF thm get_cm_restore_call_bases_below(void) {
  return cm_restore_call_bases_below;
}
PROOF static thm cm_prove_machine_return_restore(void) {
  term restored =
      `cm_restore_call (st:cm_src_state)
        (oldenv:int->int->cm_value) (oldfp:int)
        (oldregions:(cm_region)list)`;
  term final_vm =
      `tvm_jump_state (vm:tvm_state) (returnpc:int)
        (TL (TL (tvm_stack vm))) (TL (tvm_calls vm))
        (tower_setw (tvm_mem vm) 8i (oldfp:int))
        (tvm_input vm) (tvm_output vm)`;
  term body = imp_chain(TERM_LIST(
      `cm_region_prefix_safe (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (oldregions:(cm_region)list)`,
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`,
      `cm_spill_frames_generation_below (cm_state_nextgen st)
        (caller_saved:(cm_spill_frame)list)`,
      `cm_value_generation_below (cm_state_nextgen st)
        (retv:cm_value)`,
      `cm_tagged_span_valid ${restored:cm_src_state}`,
      `!addr.
         cm_live_address ${restored:cm_src_state} addr ==>
         ~(8i <= addr && addr < 16i)`,
      `cm_call_frames_store_safe CMIntTy 8i
        (calls:(cm_call_sim_frame)list)`,
      `cm_spill_frames_store_safe (p:cm_program) CMIntTy 8i
        (caller_saved:(cm_spill_frame)list)`,
      `tower_signed64 (oldfp:int)`,
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
        (vm:tvm_state)
        (CMCallSimFrame (cm_state_fp st) (oldfp:int) (returnpc:int) ::
          (calls:(cm_call_sim_frame)list))
        (CMSpillFrame (fid:int) (cm_state_fp st)
           (current_spills:(cm_spill)list) ::
         (caller_saved:(cm_spill_frame)list))
        [CMIntV 8i; CMIntV (oldfp:int); retv] []`),
      `cm_machine_state_sim (p:cm_program) ${restored:cm_src_state}
        ${final_vm:tvm_state} (calls:(cm_call_sim_frame)list)
        (caller_saved:(cm_spill_frame)list)
        [(retv:cm_value)] []`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm prefix = assume_rule(
      `cm_region_prefix_safe (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (oldregions:(cm_region)list)`);
  thm tag_below = assume_rule(
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`);
  thm spill_below = assume_rule(
      `cm_spill_frames_generation_below
        (cm_state_nextgen (st:cm_src_state))
        (caller_saved:(cm_spill_frame)list)`);
  thm value_below = assume_rule(
      `cm_value_generation_below (cm_state_nextgen (st:cm_src_state))
        (retv:cm_value)`);
  thm span_valid = assume_rule(
      `cm_tagged_span_valid ${restored:cm_src_state}`);
  thm outside = assume_rule(
      `!addr.
         cm_live_address ${restored:cm_src_state} addr ==>
         ~(8i <= addr && addr < 16i)`);
  thm calls_safe = assume_rule(
      `cm_call_frames_store_safe CMIntTy 8i
        (calls:(cm_call_sim_frame)list)`);
  thm spills_safe = assume_rule(
      `cm_spill_frames_store_safe (p:cm_program) CMIntTy 8i
        (caller_saved:(cm_spill_frame)list)`);
  thm oldfp_signed = assume_rule(`tower_signed64 (oldfp:int)`);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
        (vm:tvm_state)
        (CMCallSimFrame (cm_state_fp st) (oldfp:int) (returnpc:int) ::
          (calls:(cm_call_sim_frame)list))
        (CMSpillFrame (fid:int) (cm_state_fp st)
           (current_spills:(cm_spill)list) ::
         (caller_saved:(cm_spill_frame)list))
        [CMIntV 8i; CMIntV (oldfp:int); (retv:cm_value)] []`);
  thm parts = conv_rule(rewrite_conv(THM_LIST(
      cm_machine_sim_parts)), simulation);
  thm initialized = conjunct1_rule(parts);
  thm after_initialized = conjunct2_rule(parts);
  thm provenance = conjunct1_rule(after_initialized);
  thm after_provenance = conjunct2_rule(after_initialized);
  thm after_fp = conjunct2_rule(after_provenance);
  thm call_sim = conjunct1_rule(after_fp);
  thm after_calls = conjunct2_rule(after_fp);
  thm spill_sim = conjunct1_rule(after_calls);
  thm after_spills = conjunct2_rule(after_calls);
  thm input_equal = conjunct1_rule(after_spills);
  thm after_input = conjunct2_rule(after_spills);
  thm output_equal = conjunct1_rule(after_input);
  thm operand = conjunct2_rule(after_input);
  thm outside_expanded = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(int_arith_rule(`8i + 8i == 16i`)))), outside);
  thm restored_initialized = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `oldenv:int->int->cm_value`, `oldfp:int`,
        `oldregions:(cm_region)list`, `tvm_mem (vm:tvm_state)`),
        cm_restore_call_initialized_transport),
      prefix), initialized);
  thm new_initialized = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        restored, `tvm_mem (vm:tvm_state)`, `8i`, `oldfp:int`),
        get_cm_initialized_scratch_store_sim()),
      restored_initialized), oldfp_signed), outside_expanded);
  thm restored_provenance = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `oldenv:int->int->cm_value`, `oldfp:int`,
      `oldregions:(cm_region)list`, `tvm_mem (vm:tvm_state)`),
      cm_restore_call_provenance_transport);
  restored_provenance = match_mp_rule(restored_provenance, prefix);
  restored_provenance = match_mp_rule(restored_provenance, tag_below);
  restored_provenance = match_mp_rule(restored_provenance, provenance);
  thm new_provenance = specl_rule(TERM_LIST(
      restored, `tvm_mem (vm:tvm_state)`, `8i`, `oldfp:int`),
      get_cm_provenance_scratch_store_sim());
  new_provenance = match_mp_rule(new_provenance, restored_provenance);
  new_provenance = match_mp_rule(new_provenance, oldfp_signed);
  new_provenance = match_mp_rule(new_provenance, span_valid);
  new_provenance = match_mp_rule(new_provenance, outside_expanded);
  thm oldfp_fixed = match_mp_rule(spec_rule(
      `oldfp:int`, get_tower_wrap64_fixed()), oldfp_signed);
  thm new_fp = conv_rule(rewrite_conv(THM_LIST(oldfp_fixed)),
      specl_rule(TERM_LIST(`tvm_mem (vm:tvm_state)`, `8i`, `oldfp:int`),
        get_tower_getw_setw()));
  thm call_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_call_frames_sim_def, cm_call_sim_base_def,
      cm_call_sim_saved_def, cm_call_sim_return_def)), call_sim);
  thm calls_nonempty = conjunct1_rule(call_opened);
  thm call_tail = conjunct2_rule(conjunct2_rule(
      conjunct2_rule(call_opened)));
  thm return_equal = conjunct1_rule(conjunct2_rule(call_opened));
  thm new_calls = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `CMIntTy:cm_type`, `8i`, `oldfp:int`,
      `tvm_mem (vm:tvm_state)`,
      `calls:(cm_call_sim_frame)list`, `TL (tvm_calls vm)`),
      get_cm_call_frames_store_sim()), call_tail), calls_safe);
  new_calls = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_store_mem_def(), get_cm_store_width_def(),
      get_cm_type_int_char_distinct(), oldfp_fixed)), new_calls);
  thm spill_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_spill_frames_sim_def, cm_spill_frame_fid_def,
      cm_spill_frame_fp_def, cm_spill_frame_spills_def)), spill_sim);
  thm old_spill_tail = conjunct2_rule(spill_opened);
  thm bases = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `oldenv:int->int->cm_value`,
      `oldfp:int`, `oldregions:(cm_region)list`, `st:cm_src_state`),
      cm_restore_call_bases_below), prefix);
  thm restored_spills = specl_rule(TERM_LIST(
      `caller_saved:(cm_spill_frame)list`, `p:cm_program`,
      `st:cm_src_state`, restored, `tvm_mem (vm:tvm_state)`,
      `cm_state_nextgen (st:cm_src_state)`),
      get_cm_spill_frames_sim_bases());
  restored_spills = match_mp_rule(restored_spills, bases);
  restored_spills = match_mp_rule(restored_spills, spill_below);
  restored_spills = match_mp_rule(restored_spills, old_spill_tail);
  thm new_spills = specl_rule(TERM_LIST(
      `p:cm_program`, restored, `tvm_mem (vm:tvm_state)`,
      `8i`, `oldfp:int`, `caller_saved:(cm_spill_frame)list`),
      get_cm_spill_frames_scratch_store_sim());
  new_spills = match_mp_rule(new_spills, restored_spills);
  new_spills = match_mp_rule(new_spills, spills_safe);
  new_spills = match_mp_rule(new_spills, oldfp_signed);
  thm old_stack = conv_rule(rewrite_conv(THM_LIST(
      cm_operand_suffix_sim_def)), operand);
  thm trimmed_stack = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        old_stack, cm_encode_values_def,
        get_theorem_by_name("APPEND"), get_theorem_by_name("TL"))),
      `TL (TL (tvm_stack (vm:tvm_state))) ==
       cm_encode_values (st:cm_src_state) [(retv:cm_value)] ++ []`));
  thm old_operand = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_operand_suffix_sim_def)),
      `cm_operand_suffix_sim (st:cm_src_state) [(retv:cm_value)] []
        (TL (TL (tvm_stack (vm:tvm_state))))`)), trimmed_stack);
  thm values_below = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_values_generation_below_def, value_below)),
      `cm_values_generation_below (cm_state_nextgen (st:cm_src_state))
        [(retv:cm_value)]`));
  thm new_operand = specl_rule(TERM_LIST(
      `st:cm_src_state`, restored, `[(retv:cm_value)]`,
      `[]:(int)list`, `TL (TL (tvm_stack (vm:tvm_state)))`,
      `cm_state_nextgen (st:cm_src_state)`),
      get_cm_operand_suffix_sim_bases());
  new_operand = match_mp_rule(new_operand, bases);
  new_operand = match_mp_rule(new_operand, values_below);
  new_operand = match_mp_rule(new_operand, old_operand);
  thm result = conj_rule(new_initialized,
      conj_rule(new_provenance,
      conj_rule(new_fp,
      conj_rule(new_calls,
      conj_rule(new_spills,
      conj_rule(input_equal,
      conj_rule(output_equal, new_operand)))))));
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_restore_call_def());
  vector_add(&rules, cm_machine_sim_parts);
  vector_add(&rules, get_tvm_jump_state_def());
  vector_add(&rules, get_tvm_state_selectors_def());
  vector_add(&rules, return_equal);
  vector_add(&rules, calls_nonempty);
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  ACCEPT_TAC(opened, conv_rule(reduce_rewrite_conv(rules), result));
  return gnode_prove(root);
}
PROOF static thm cm_machine_return_restore =
    cm_prove_machine_return_restore();



PROOF static thm cm_prove_target_load_saved_fp(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (oldfp:int) (returnpc:int)
         (calls:(cm_call_sim_frame)list)
         (values:(cm_value)list) (ann:cm_annotation)
         (target:tvm_task) (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst TVMLoadOp 0i :: rest) ==>
         cm_ann_calls ann ==
           CMCallSimFrame (cm_state_fp st) oldfp returnpc :: calls ==>
         tower_signed64 (cm_state_fp st) ==>
         tower_word_valid (cm_state_fp st) ==>
         tower_signed64 oldfp ==>
         cm_running_target_sim p fid st
           (CMIntV (cm_state_fp st) :: values) ann target ==>
         cm_running_target_sim p fid st
           (CMIntV oldfp :: values)
           (cm_ann_linear [TVMInst TVMLoadOp 0i] ann)
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMLoadOp 0i :: (rest:(tvm_inst)list))`);
  thm calls_shape = assume_rule(
      `cm_ann_calls (ann:cm_annotation) ==
       CMCallSimFrame (cm_state_fp (st:cm_src_state))
         (oldfp:int) (returnpc:int) ::
       (calls:(cm_call_sim_frame)list)`);
  thm fp_signed = assume_rule(
      `tower_signed64 (cm_state_fp (st:cm_src_state))`);
  thm fp_word_valid = assume_rule(
      `tower_word_valid (cm_state_fp (st:cm_src_state))`);
  thm oldfp_signed = assume_rule(`tower_signed64 (oldfp:int)`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        (CMIntV (cm_state_fp st) :: (values:(cm_value)list))
        (ann:cm_annotation) (target:tvm_task)`);
  thm expanded = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_running_target_sim_def)),
      concl(running)), running);
  thm body = assume_rule(
      `(target:tvm_task) ==
          TVMRunTask (cm_compile_model (p:cm_program)) (vm:tvm_state) &&
       tvm_pc vm == cm_ann_pc (ann:cm_annotation) &&
       cm_machine_state_sim p (st:cm_src_state) vm
         (cm_ann_calls ann)
         (cm_active_spill_frames (fid:int) st ann)
         (CMIntV (cm_state_fp st) :: (values:(cm_value)list)) []`);
  thm target_equal = conjunct1_rule(body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(body));
  thm machine = conjunct2_rule(conjunct2_rule(body));
  thm stack_length = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `CMIntV (cm_state_fp st) :: (values:(cm_value)list)`,
      `[]:(int)list`), get_cm_machine_sim_stack_length()), machine);
  thm stack_nonempty = mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) ==
         (1i + ilength (values:(cm_value)list)) + 0i ==>
       0i <= ilength values ==>
       1i <= ilength (tvm_stack vm)`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  stack_nonempty = match_mp_rule(stack_nonempty,
      ispec_rule(`values:(cm_value)list`,
        get_theorem_by_name("ILENGTH_NONNEG")));
  thm stack_head = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `CMIntV (cm_state_fp st)`, `values:(cm_value)list`,
      `[]:(int)list`), cm_machine_sim_stack_head), machine);
  thm fp_fixed = mp_rule(spec_rule(
      `cm_state_fp (st:cm_src_state)`, get_tower_wrap64_fixed()),
      fp_signed);
  thm oldfp_fixed = mp_rule(spec_rule(
      `oldfp:int`, get_tower_wrap64_fixed()), oldfp_signed);
  thm address_valid = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        conjunct1_rule(stack_head), get_cm_value_number_def(),
        get_tower_wrap64_def(), fp_fixed, fp_word_valid)),
      `tower_word_valid (HD (tvm_stack (vm:tvm_state)))`));
  thm machine_parts = conv_rule(rewrite_conv(THM_LIST(
      cm_machine_sim_parts)), machine);
  thm call_sim = conjunct1_rule(conjunct2_rule(conjunct2_rule(
      conjunct2_rule(machine_parts))));
  thm call_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      calls_shape, cm_call_frames_sim_def,
      cm_call_sim_base_def, cm_call_sim_saved_def,
      cm_call_sim_return_def)), call_sim);
  thm saved_word = conjunct1_rule(conjunct2_rule(
      conjunct2_rule(call_opened)));
  thm operation_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_value_number_def(), get_tower_wrap64_def(),
        fp_fixed, oldfp_fixed)),
      `tower_getw (tvm_mem (vm:tvm_state))
          (cm_value_number (st:cm_src_state)
            (CMIntV (cm_state_fp st))) ==
       cm_value_number st (CMIntV (oldfp:int))`);
  thm operation = eq_mp_rule(sym_rule(operation_view), saved_word);
  term next =
      `tvm_next_state (vm:tvm_state)
        (tower_getw (tvm_mem vm) (HD (tvm_stack vm)) ::
         TL (tvm_stack vm))
        (tvm_calls vm) (tvm_mem vm)
        (tvm_input vm) (tvm_output vm)`;
  thm action = specl_rule(TERM_LIST(
      `tvm_object_code (cm_compile_model (p:cm_program))`,
      `0i:int`, `vm:tvm_state`), get_tvm_load_transition());
  action = conv_rule(reduce_rewrite_conv(THM_LIST(
      stack_nonempty, address_valid)), action);
  thm compiled_code = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (tvm_pc (vm:tvm_state))
        (TVMInst TVMLoadOp 0i :: (rest:(tvm_inst)list))`));
  thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
      `TVMLoadOp:tvm_opcode`, `0i:int`,
      `rest:(tvm_inst)list`, next),
      cm_tvm_state_iter_one), compiled_code), action);
  stepped = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(target_equal))), stepped);
  thm load_effect = beta_norm(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `CMIntV (cm_state_fp st)`, `values:(cm_value)list`,
      `[]:(int)list`, `CMIntV (oldfp:int)`,
      `(\address:int. tower_getw
          (tvm_mem (vm:tvm_state)) address)`),
      get_cm_machine_unary_operation()));
  thm machine_after = match_mp_rule(
      match_mp_rule(load_effect, machine), operation);
  term updated =
      `cm_ann_linear [TVMInst TVMLoadOp 0i]
        (ann:cm_annotation)`;
  thm next_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_tvm_next_state_def(), get_tvm_state_selectors_def(),
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
        get_theorem_by_name("ILENGTH_DEF"), pc_equal)),
      `tvm_pc ${next:tvm_state} ==
       cm_ann_pc ${updated:cm_annotation}`));
  thm normalized_body =
      conj_rule(stepped, conj_rule(next_pc, machine_after));
  thm_list update_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_pc_def, cm_ann_calls_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_active_spill_frames_def,
      get_theorem_by_name("ILENGTH_DEF"));
  normalized_body =
      conv_rule(reduce_rewrite_conv(update_rules), normalized_body);
  term exists_goal =
      `?next_vm.
         tvm_iter 1 (target:tvm_task) ==
           TVMRunTask (cm_compile_model (p:cm_program)) next_vm &&
         tvm_pc next_vm == cm_ann_pc ${updated:cm_annotation} &&
         cm_machine_state_sim p (st:cm_src_state) next_vm
           (cm_ann_calls ${updated:cm_annotation})
           (cm_active_spill_frames (fid:int) st
             ${updated:cm_annotation})
           (CMIntV (oldfp:int) :: (values:(cm_value)list)) []`;
  dest_exists_results exists_parts = dest_exists(exists_goal);
  term instantiated_body = subst_one(next, exists_parts.v, exists_parts.tm);
  thm body_reduction = apply_conversion(
      reduce_rewrite_conv(update_rules), instantiated_body);
  thm adjusted_body = eq_mp_rule(
      sym_rule(body_reduction), normalized_body);
  thm witness = exists_rule(exists_goal, next, adjusted_body);
  thm selected = choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_running_target_sim_def)));
  ACCEPT_TAC(opened, selected);
  return gnode_prove(root);
}
PROOF thm cm_target_load_saved_fp =
    cm_prove_target_load_saved_fp();

PROOF thm get_cm_target_load_saved_fp(void) {
  return cm_target_load_saved_fp;
}
PROOF static thm cm_prove_target_return_epilogue(void) {
  term caller_saved =
      `CMSpillFrame (caller:int) (oldfp:int)
         (caller_spills:(cm_spill)list) ::
       (saved:(cm_spill_frame)list)`;
  term restored =
      `cm_restore_call (st:cm_src_state)
        (oldenv:int->int->cm_value) (oldfp:int)
        (oldregions:(cm_region)list)`;
  term final_ann =
      `cm_ann_leave_call (returnpc:int) (ann:cm_annotation)`;
  term body = imp_chain(TERM_LIST(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMStoreOp 0i :: TVMInst TVMRetOp 0i ::
          (rest:(tvm_inst)list))`,
      `cm_ann_calls (ann:cm_annotation) ==
        CMCallSimFrame (cm_state_fp (st:cm_src_state))
          (oldfp:int) (returnpc:int) ::
        (calls:(cm_call_sim_frame)list)`,
      `cm_ann_saved (ann:cm_annotation) ==
        ${caller_saved:(cm_spill_frame)list}`,
      `cm_region_prefix_safe (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (oldregions:(cm_region)list)`,
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`,
      `cm_spill_frames_generation_below (cm_state_nextgen st)
        ${caller_saved:(cm_spill_frame)list}`,
      `cm_value_generation_below (cm_state_nextgen st)
        (retv:cm_value)`,
      `cm_tagged_span_valid ${restored:cm_src_state}`,
      `!addr.
         cm_live_address ${restored:cm_src_state} addr ==>
         ~(8i <= addr && addr < 16i)`,
      `cm_call_frames_store_safe CMIntTy 8i
        (calls:(cm_call_sim_frame)list)`,
      `cm_spill_frames_store_safe (p:cm_program) CMIntTy 8i
        ${caller_saved:(cm_spill_frame)list}`,
      `tower_signed64 (oldfp:int)`,
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        [CMIntV 8i; CMIntV (oldfp:int); (retv:cm_value)]
        (ann:cm_annotation) (target:tvm_task)`),
      `cm_running_target_sim (p:cm_program) (caller:int)
        ${restored:cm_src_state} [(retv:cm_value)]
        ${final_ann:cm_annotation} (tvm_iter 2 (target:tvm_task))`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMStoreOp 0i :: TVMInst TVMRetOp 0i ::
          (rest:(tvm_inst)list))`);
  thm calls_shape = assume_rule(
      `cm_ann_calls (ann:cm_annotation) ==
       CMCallSimFrame (cm_state_fp (st:cm_src_state))
         (oldfp:int) (returnpc:int) ::
       (calls:(cm_call_sim_frame)list)`);
  thm saved_shape = assume_rule(
      `cm_ann_saved (ann:cm_annotation) ==
       ${caller_saved:(cm_spill_frame)list}`);
  thm prefix = assume_rule(
      `cm_region_prefix_safe (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (oldregions:(cm_region)list)`);
  thm tag_below = assume_rule(
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`);
  thm spill_below = assume_rule(
      `cm_spill_frames_generation_below
        (cm_state_nextgen (st:cm_src_state))
        ${caller_saved:(cm_spill_frame)list}`);
  thm value_below = assume_rule(
      `cm_value_generation_below (cm_state_nextgen (st:cm_src_state))
        (retv:cm_value)`);
  thm span_valid = assume_rule(
      `cm_tagged_span_valid ${restored:cm_src_state}`);
  thm outside = assume_rule(
      `!addr.
         cm_live_address ${restored:cm_src_state} addr ==>
         ~(8i <= addr && addr < 16i)`);
  thm calls_safe = assume_rule(
      `cm_call_frames_store_safe CMIntTy 8i
        (calls:(cm_call_sim_frame)list)`);
  thm spills_safe = assume_rule(
      `cm_spill_frames_store_safe (p:cm_program) CMIntTy 8i
        ${caller_saved:(cm_spill_frame)list}`);
  thm oldfp_signed = assume_rule(`tower_signed64 (oldfp:int)`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        [CMIntV 8i; CMIntV (oldfp:int); (retv:cm_value)]
        (ann:cm_annotation) (target:tvm_task)`);
  thm expanded = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_running_target_sim_def)),
      concl(running)), running);
  thm selected_body = assume_rule(
      `(target:tvm_task) ==
          TVMRunTask (cm_compile_model (p:cm_program)) (vm:tvm_state) &&
       tvm_pc vm == cm_ann_pc (ann:cm_annotation) &&
       cm_machine_state_sim p (st:cm_src_state) vm
         (cm_ann_calls ann)
         (cm_active_spill_frames (fid:int) st ann)
         [CMIntV 8i; CMIntV (oldfp:int); (retv:cm_value)] []`);
  thm target_equal = conjunct1_rule(selected_body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(selected_body));
  thm machine = conjunct2_rule(conjunct2_rule(selected_body));
  thm machine_shaped = conv_rule(reduce_rewrite_conv(THM_LIST(
      calls_shape, saved_shape, cm_active_spill_frames_def,
      cm_ann_spills_def, cm_ann_saved_def)), machine);
  term old_calls =
      `CMCallSimFrame (cm_state_fp (st:cm_src_state))
        (oldfp:int) (returnpc:int) ::
       (calls:(cm_call_sim_frame)list)`;
  term old_spills =
      `CMSpillFrame (fid:int) (cm_state_fp (st:cm_src_state))
         (cm_ann_spills (ann:cm_annotation)) ::
       ${caller_saved:(cm_spill_frame)list}`;
  thm stack_length = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      old_calls, old_spills,
      `[CMIntV 8i; CMIntV (oldfp:int); (retv:cm_value)]`,
      `[]:(int)list`), get_cm_machine_sim_stack_length()),
      machine_shaped);
  thm stack_two = match_mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) == 3i ==>
       2i <= ilength (tvm_stack vm)`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  thm stack_shape = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      old_calls, old_spills,
      `[CMIntV 8i; CMIntV (oldfp:int); (retv:cm_value)]`,
      `[]:(int)list`), get_cm_machine_sim_stack_shape()),
      machine_shaped);
  thm eight_fixed = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_tower_wrap64_def())),
      `tower_wrap64 8i == 8i`));
  thm oldfp_fixed = match_mp_rule(spec_rule(
      `oldfp:int`, get_tower_wrap64_fixed()), oldfp_signed);
  thm head_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        stack_shape, cm_encode_values_def, get_cm_value_number_def(),
        eight_fixed, oldfp_fixed, get_theorem_by_name("APPEND"),
        get_theorem_by_name("HD"))),
      `HD (tvm_stack (vm:tvm_state)) == 8i`));
  thm second_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        stack_shape, cm_encode_values_def, get_cm_value_number_def(),
        eight_fixed, oldfp_fixed, get_theorem_by_name("APPEND"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
      `HD (TL (tvm_stack (vm:tvm_state))) == (oldfp:int)`));
  thm address_valid = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        head_equal, get_tower_word_valid_def())),
      `tower_word_valid (HD (tvm_stack (vm:tvm_state)))`));
  term stored =
      `tvm_next_state (vm:tvm_state)
        (TL (TL (tvm_stack vm))) (tvm_calls vm)
        (tower_setw (tvm_mem vm) 8i (oldfp:int))
        (tvm_input vm) (tvm_output vm)`;
  thm store_action = specl_rule(TERM_LIST(
      `tvm_object_code (cm_compile_model (p:cm_program))`,
      `0i:int`, `vm:tvm_state`), get_tvm_store_transition());
  store_action = conv_rule(reduce_rewrite_conv(THM_LIST(
      stack_two, address_valid, head_equal, second_equal)), store_action);
  thm compiled_store = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (tvm_pc (vm:tvm_state))
        (TVMInst TVMStoreOp 0i :: TVMInst TVMRetOp 0i ::
          (rest:(tvm_inst)list))`));
  thm first_step = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
      `TVMStoreOp:tvm_opcode`, `0i:int`,
      `TVMInst TVMRetOp 0i :: (rest:(tvm_inst)list)`, stored),
      cm_tvm_state_iter_one), compiled_store), store_action);
  first_step = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(target_equal))), first_step);
  thm machine_parts = conv_rule(rewrite_conv(THM_LIST(
      cm_machine_sim_parts)), machine_shaped);
  thm call_sim = conjunct1_rule(conjunct2_rule(conjunct2_rule(
      conjunct2_rule(machine_parts))));
  thm call_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_call_frames_sim_def, cm_call_sim_base_def,
      cm_call_sim_saved_def, cm_call_sim_return_def)), call_sim);
  thm calls_nonempty = conjunct1_rule(call_opened);
  thm return_equal = conjunct1_rule(conjunct2_rule(call_opened));
  thm calls_cons = match_mp_rule(
      ispec_rule(`tvm_calls (vm:tvm_state)`,
        get_theorem_by_name("CONS_HD_TL")), calls_nonempty);
  thm calls_length = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("ILENGTH_DEF"))), beta_norm(ap_term_rule(
        `\xs:(int)list. ilength xs`, calls_cons)));
  thm calls_bound = match_mp_rule(match_mp_rule(int_arith_rule(
      `ilength (tvm_calls (vm:tvm_state)) ==
          1i + ilength (TL (tvm_calls vm)) ==>
       0i <= ilength (TL (tvm_calls vm)) ==>
       1i <= ilength (tvm_calls vm)`),
      calls_length), ispec_rule(`TL (tvm_calls (vm:tvm_state))`,
        get_theorem_by_name("ILENGTH_NONNEG")));
  thm ret_rule = ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`,
      `cm_ann_pc (ann:cm_annotation)`,
      `[TVMInst TVMStoreOp 0i]`,
      `TVMInst TVMRetOp 0i :: (rest:(tvm_inst)list)`),
      cm_code_at_append_right);
  ret_rule = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("ILENGTH_DEF"))), ret_rule);
  thm ret_code = match_mp_rule(ret_rule, code_at);
  term returned =
      `tvm_jump_state (vm:tvm_state) (returnpc:int)
        (TL (TL (tvm_stack vm))) (TL (tvm_calls vm))
        (tower_setw (tvm_mem vm) 8i (oldfp:int))
        (tvm_input vm) (tvm_output vm)`;
  thm ret_action = specl_rule(TERM_LIST(
      `tvm_object_code (cm_compile_model (p:cm_program))`,
      `0i:int`, stored), get_tvm_ret_transition());
  thm_list ret_action_rules = THM_LIST(
      get_tvm_next_state_def(), get_tvm_jump_state_def(),
      get_tvm_state_selectors_def(), calls_bound, return_equal);
  ret_action = conv_rule(
      reduce_rewrite_conv(ret_action_rules), ret_action);
  term ret_action_term =
      `tvm_inst_step
         (tvm_object_code (cm_compile_model (p:cm_program)))
         TVMRetOp 0i ${stored:tvm_state} ==
       TVMStepState ${returned:tvm_state}`;
  thm ret_action_view = apply_conversion(
      reduce_rewrite_conv(ret_action_rules), ret_action_term);
  ret_action = eq_mp_rule(sym_rule(ret_action_view), ret_action);
  thm compiled_ret = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        get_tvm_next_state_def(), get_tvm_state_selectors_def(),
        pc_equal, ret_code)),
      `cm_code_at
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (tvm_pc ${stored:tvm_state})
        (TVMInst TVMRetOp 0i :: (rest:(tvm_inst)list))`));
  thm second_step = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, stored,
      `TVMRetOp:tvm_opcode`, `0i:int`, `rest:(tvm_inst)list`,
      returned), cm_tvm_state_iter_one), compiled_ret), ret_action);
  thm two_steps = specl_rule(TERM_LIST(
      `1:num`, `1:num`, `target:tvm_task`,
      `TVMRunTask (cm_compile_model (p:cm_program)) ${stored:tvm_state}`,
      `TVMRunTask (cm_compile_model (p:cm_program)) ${returned:tvm_state}`),
      cm_tvm_iter_compose);
  two_steps = match_mp_rule(two_steps, first_step);
  two_steps = match_mp_rule(two_steps, second_step);
  two_steps = conv_rule(rewrite_conv(THM_LIST(
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `(1:num) + 1`))), two_steps);
  thm machine_after = cm_machine_return_restore;
  machine_after = specl_rule(TERM_LIST(
      `fid:int`, `cm_ann_spills (ann:cm_annotation)`,
      `p:cm_program`, `st:cm_src_state`,
      `oldenv:int->int->cm_value`, `oldregions:(cm_region)list`,
      `returnpc:int`, `oldfp:int`, `vm:tvm_state`,
      `calls:(cm_call_sim_frame)list`, caller_saved,
      `retv:cm_value`), machine_after);
  machine_after = match_mp_rule(machine_after, prefix);
  machine_after = match_mp_rule(machine_after, tag_below);
  machine_after = match_mp_rule(machine_after, spill_below);
  machine_after = match_mp_rule(machine_after, value_below);
  machine_after = match_mp_rule(machine_after, span_valid);
  machine_after = match_mp_rule(machine_after, outside);
  machine_after = match_mp_rule(machine_after, calls_safe);
  machine_after = match_mp_rule(machine_after, spills_safe);
  machine_after = match_mp_rule(machine_after, oldfp_signed);
  machine_after = match_mp_rule(machine_after, machine_shaped);
  thm next_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_tvm_jump_state_def(), get_tvm_state_selectors_def(),
        cm_ann_leave_call_def, cm_ann_pc_def)),
      `tvm_pc ${returned:tvm_state} ==
       cm_ann_pc ${final_ann:cm_annotation}`));
  thm normalized_body =
      conj_rule(two_steps, conj_rule(next_pc, machine_after));
  thm_list update_rules = get_cm_state_core_defs();
  vector_add(&update_rules, get_cm_restore_call_def());
  vector_add(&update_rules, cm_ann_leave_call_def);
  vector_add(&update_rules, cm_ann_pc_def);
  vector_add(&update_rules, cm_ann_cursors_def);
  vector_add(&update_rules, cm_ann_spills_def);
  vector_add(&update_rules, cm_ann_saved_def);
  vector_add(&update_rules, cm_ann_calls_def);
  vector_add(&update_rules, cm_spill_frame_spills_def);
  vector_add(&update_rules, cm_active_spill_frames_def);
  vector_add(&update_rules, get_theorem_by_name("HD"));
  vector_add(&update_rules, get_theorem_by_name("TL"));
  vector_add(&update_rules, get_theorem_by_name("NOT_CONS_NIL"));
  vector_add(&update_rules, calls_shape);
  vector_add(&update_rules, saved_shape);
  normalized_body = conv_rule(
      reduce_rewrite_conv(update_rules), normalized_body);
  term exists_goal =
      `?next_vm.
         tvm_iter 2 (target:tvm_task) ==
           TVMRunTask (cm_compile_model (p:cm_program)) next_vm &&
         tvm_pc next_vm == cm_ann_pc ${final_ann:cm_annotation} &&
         cm_machine_state_sim p ${restored:cm_src_state} next_vm
           (cm_ann_calls ${final_ann:cm_annotation})
           (cm_active_spill_frames (caller:int) ${restored:cm_src_state}
             ${final_ann:cm_annotation})
           [(retv:cm_value)] []`;
  dest_exists_results exists_parts = dest_exists(exists_goal);
  term instantiated_body =
      subst_one(returned, exists_parts.v, exists_parts.tm);
  thm body_reduction = apply_conversion(
      reduce_rewrite_conv(update_rules), instantiated_body);
  thm adjusted_body =
      eq_mp_rule(sym_rule(body_reduction), normalized_body);
  thm witness =
      exists_rule(exists_goal, returned, adjusted_body);
  thm selected =
      choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_running_target_sim_def)));
  ACCEPT_TAC(opened, selected);
  return gnode_prove(root);
}
PROOF thm cm_target_return_epilogue =
    cm_prove_target_return_epilogue();

PROOF thm get_cm_target_return_epilogue(void) {
  return cm_target_return_epilogue;
}


PROOF static int cmc_preservation_target_return_machine_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_return_machine_axioms_before,
      "cmc_preservation_target_return_machine introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_load_saved_fp)) == 0 &&
      vector_size(hyp(cm_target_return_epilogue)) == 0,
      "return machine theorem has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_return_machine_checks =
    cmc_preservation_target_return_machine_final_checks();
