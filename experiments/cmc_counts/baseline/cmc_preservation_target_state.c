#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_state.h"
#include "userlib/proof_patterns.h"

#require "userlib/proof_patterns.c"
#require "cmc_preservation_target_machine.c"
#require "cmc_preservation_tagged_allocation.c"
#require "cmc_preservation_call_transport.c"

PROOF static size_t _cmc_preservation_target_state_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_target_state_local_base(void) {
  return `cm_local_base (p:cm_program) (fid:int) (slot:int)
      (cm_state_fp (st:cm_src_state))`;
}

PROOF static term cm_target_state_local_width(void) {
  return `cm_slot_size (cm_program_structs (p:cm_program))
      (inth (slot:int) (cm_function_locals
        (inth (fid:int) (cm_program_functions p))))`;
}

PROOF static term cm_target_state_fresh_region(void) {
  term base = cm_target_state_local_base();
  term width = cm_target_state_local_width();
  return `CMRegion (cm_state_nextgen (st:cm_src_state))
      ${base:int} 0i ${width:int} T T`;
}

PROOF static thm cm_prove_activate_regions_bases(void) {
  term fresh = cm_target_state_fresh_region();
  term old_regions = `cm_state_regions (st:cm_src_state)`;
  term nextgen = `cm_state_nextgen (st:cm_src_state)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (slot:int) (st:cm_src_state).
         cm_region_bases_below_equal
           (cm_state_regions (cm_activate_local p fid slot st))
           (cm_state_regions st) (cm_state_nextgen st)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm lower_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_region_gen_def())),
      `${nextgen:int} <= cm_region_gen ${fresh:cm_region}`);
  thm lower = eq_mp_rule(sym_rule(lower_view),
      int_arith_rule(`${nextgen:int} <= ${nextgen:int}`));
  thm result = match_mp_rule(specl_rule(TERM_LIST(
      fresh, old_regions, nextgen), cm_region_bases_fresh_cons), lower);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_activate_local_def());
  vector_add(&rules, get_cm_region_gen_def());
  thm normalized = conv_rule(reduce_rewrite_conv(rules), result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}
PROOF static thm cm_activate_regions_bases =
    cm_prove_activate_regions_bases();

PROOF static thm cm_prove_activate_initialized_transport(void) {
  term activated =
      `cm_activate_local (p:cm_program) (fid:int) (slot:int)
        (st:cm_src_state)`;
  term base = cm_target_state_local_base();
  term width = cm_target_state_local_width();
  term outside =
      `~(${base:int} <= (addr:int) && addr < ${base:int} + ${width:int})`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (slot:int) (st:cm_src_state)
         (mem:int->int).
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         cm_initialized_bytes_sim st mem ==>
         cm_initialized_bytes_sim
           (cm_activate_local p fid slot st) mem`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm before = assume_rule(
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`);
  thm old_sim = conv_rule(rewrite_conv(THM_LIST(
      cm_initialized_bytes_sim_def)), assume_rule(
        `cm_initialized_bytes_sim (st:cm_src_state) (mem:int->int)`));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_initialized_bytes_sim_def)));
  gnode point = AUTO_INTROS_TAC(opened);
  thm new_parts = assume_rule(
      `cm_state_init ${activated:cm_src_state} (addr:int) &&
       cm_live_address ${activated:cm_src_state} addr`);
  thm_list state_rules = get_cm_state_core_defs();
  vector_add(&state_rules, get_cm_activate_local_def());
  vector_add(&state_rules, get_cm_clear_init_def());
  thm new_init = conv_rule(reduce_rewrite_conv(state_rules),
      conjunct1_rule(new_parts));
  thm old_init = conjunct1_rule(new_init);
  thm outside_fact = conjunct2_rule(new_init);
  thm live_cases = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `slot:int`, `st:cm_src_state`,
      `addr:int`), cm_activate_live_old_or_local), before),
      conjunct2_rule(new_parts));
  dest_disj_results live_parts = dest_disj(concl(live_cases));
  thm old_live_case = assume_rule(live_parts.tm1);
  thm local_case = assume_rule(live_parts.tm2);
  thm impossible = mp_rule(int_arith_rule(mk_imp(
      concl(conj_rule(outside_fact, local_case)), `F`)),
      conj_rule(outside_fact, local_case));
  thm old_live = disj_cases_rule(live_cases, old_live_case,
      false_elim_rule(impossible, live_parts.tm1));
  thm result = match_mp_rule(spec_rule(`addr:int`, old_sim),
      conj_rule(old_init, old_live));
  thm normalized = conv_rule(reduce_rewrite_conv(state_rules), result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(state_rules), goal_ccl(point->g));
  ACCEPT_TAC(point, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}
PROOF static thm cm_activate_initialized_transport =
    cm_prove_activate_initialized_transport();

PROOF static thm cm_prove_activate_provenance_transport(void) {
  term activated =
      `cm_activate_local (p:cm_program) (fid:int) (slot:int)
        (st:cm_src_state)`;
  term base = cm_target_state_local_base();
  term width = cm_target_state_local_width();
  term outside =
      `~(${base:int} <= (addr:int) && addr < ${base:int} + ${width:int})`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (slot:int) (st:cm_src_state)
         (mem:int->int).
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         cm_state_tags_generation_below st
           (cm_state_nextgen st) ==>
         0i <
           cm_slot_size (cm_program_structs p)
             (inth slot (cm_function_locals
               (inth fid (cm_program_functions p)))) ==>
         cm_stored_provenance_sim st mem ==>
         cm_stored_provenance_sim
           (cm_activate_local p fid slot st) mem`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm before = assume_rule(
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`);
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
      `cm_state_tagged ${activated:cm_src_state} (addr:int) &&
       cm_live_address ${activated:cm_src_state} addr`);
  thm_list state_rules = get_cm_state_core_defs();
  vector_add(&state_rules, get_cm_activate_local_def());
  vector_add(&state_rules, get_cm_clear_init_def());
  vector_add(&state_rules, get_cm_clear_tagged_def());
  thm new_tagged = conv_rule(reduce_rewrite_conv(state_rules),
      conjunct1_rule(new_parts));
  thm old_tagged = conjunct1_rule(new_tagged);
  thm no_overlap = conjunct2_rule(new_tagged);
  thm width_positive = assume_rule(`0i < ${width:int}`);
  thm outside_fact = mp_rule(int_arith_rule(mk_imp(
      concl(conj_rule(width_positive, no_overlap)), outside)),
      conj_rule(width_positive, no_overlap));
  thm live_cases = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `slot:int`, `st:cm_src_state`,
      `addr:int`), cm_activate_live_old_or_local), before),
      conjunct2_rule(new_parts));
  dest_disj_results live_parts = dest_disj(concl(live_cases));
  thm old_live_case = assume_rule(live_parts.tm1);
  thm local_case = assume_rule(live_parts.tm2);
  thm impossible = mp_rule(int_arith_rule(mk_imp(
      concl(conj_rule(outside_fact, local_case)), `F`)),
      conj_rule(outside_fact, local_case));
  thm old_live = disj_cases_rule(live_cases, old_live_case,
      false_elim_rule(impossible, live_parts.tm1));
  thm old_point = match_mp_rule(spec_rule(`addr:int`, old_sim),
      conj_rule(old_tagged, old_live));
  thm new_init_raw = conj_rule(conjunct1_rule(old_point), outside_fact);
  thm new_init = eq_mp_rule(sym_rule(apply_conversion(
      reduce_rewrite_conv(state_rules),
      `cm_state_init ${activated:cm_src_state} (addr:int)`)),
      new_init_raw);
  thm below_open = conv_rule(rewrite_conv(THM_LIST(
      cm_state_tags_generation_below_def)), tag_below);
  thm value_below = match_mp_rule(spec_rule(`addr:int`, below_open),
      old_tagged);
  thm number = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_state_tags (st:cm_src_state) (addr:int)`,
      `st:cm_src_state`, activated, `cm_state_nextgen st`),
      cm_value_number_bases),
      specl_rule(TERM_LIST(`p:cm_program`, `fid:int`, `slot:int`,
        `st:cm_src_state`), cm_activate_regions_bases)), value_below);
  thm word = trans_rule(conjunct2_rule(old_point), sym_rule(number));
  thm result = conj_rule(new_init, word);
  thm normalized = conv_rule(reduce_rewrite_conv(state_rules), result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(state_rules), goal_ccl(point->g));
  ACCEPT_TAC(point, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}
PROOF static thm cm_activate_provenance_transport =
    cm_prove_activate_provenance_transport();

PROOF static thm cm_prove_machine_activate_local_empty(void) {
  term activated =
      `cm_activate_local (p:cm_program) (fid:int) (slot:int)
        (st:cm_src_state)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (slot:int) (st:cm_src_state)
         (vm:tvm_state) (calls:(cm_call_sim_frame)list)
         (spills:(cm_spill_frame)list).
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         cm_state_tags_generation_below st
           (cm_state_nextgen st) ==>
         0i <
           cm_slot_size (cm_program_structs p)
             (inth slot (cm_function_locals
               (inth fid (cm_program_functions p)))) ==>
         cm_spill_frames_generation_below
           (cm_state_nextgen st) spills ==>
         cm_machine_state_sim p st vm calls spills [] [] ==>
         cm_machine_state_sim p
           (cm_activate_local p fid slot st) vm calls spills [] []`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm before = assume_rule(
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`);
  thm tag_below = assume_rule(
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`);
  thm spill_below = assume_rule(
      `cm_spill_frames_generation_below (cm_state_nextgen st)
        (spills:(cm_spill_frame)list)`);
  thm old_sim = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
        (vm:tvm_state) (calls:(cm_call_sim_frame)list)
        (spills:(cm_spill_frame)list) [] []`);
  thm parts = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_machine_state_sim_def)), concl(old_sim)),
      old_sim);
  thm initialized = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `slot:int`, `st:cm_src_state`,
      `tvm_mem (vm:tvm_state)`), cm_activate_initialized_transport),
      before), conjunct1_rule(parts));
  parts = conjunct2_rule(parts);
  thm provenance = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(`p:cm_program`, `fid:int`,
        `slot:int`, `st:cm_src_state`, `tvm_mem (vm:tvm_state)`),
        cm_activate_provenance_transport), before), tag_below),
      assume_rule(`0i < ${cm_target_state_local_width():int}`)),
      conjunct1_rule(parts));
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
  thm bases = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `slot:int`, `st:cm_src_state`),
      cm_activate_regions_bases);
  thm new_spills = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(`spills:(cm_spill_frame)list`,
        `p:cm_program`, `st:cm_src_state`, activated,
        `tvm_mem (vm:tvm_state)`, `cm_state_nextgen st`),
        cm_spill_frames_sim_bases), bases), spill_below), old_spills);
  thm_list state_rules = get_cm_state_core_defs();
  vector_add(&state_rules, get_cm_activate_local_def());
  thm fp_equal = apply_conversion(reduce_rewrite_conv(state_rules),
      `cm_state_fp ${activated:cm_src_state}`);
  thm input_equal = apply_conversion(reduce_rewrite_conv(state_rules),
      `cm_state_input ${activated:cm_src_state}`);
  thm output_equal = apply_conversion(reduce_rewrite_conv(state_rules),
      `cm_state_output ${activated:cm_src_state}`);
  frame_pointer = trans_rule(frame_pointer, sym_rule(fp_equal));
  input = trans_rule(input, sym_rule(input_equal));
  output = trans_rule(output, sym_rule(output_equal));
  thm empty_below = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_values_generation_below_def)),
      `cm_values_generation_below (cm_state_nextgen st)
        ([]:(cm_value)list)`));
  operands = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(`st:cm_src_state`, activated,
        `[]:(cm_value)list`, `[]:(int)list`,
        `tvm_stack (vm:tvm_state)`, `cm_state_nextgen st`),
        cm_operand_suffix_sim_bases), bases), empty_below), operands);
  thm rebuilt = conj_rule(initialized, conj_rule(provenance,
      conj_rule(frame_pointer, conj_rule(calls_sim,
        conj_rule(new_spills, conj_rule(input,
          conj_rule(output, operands)))))));
  thm target_view = apply_conversion(
      rewrite_conv(THM_LIST(cm_machine_state_sim_def)),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), rebuilt));
  return gnode_prove(root);
}
PROOF static thm cm_machine_activate_local_empty =
    cm_prove_machine_activate_local_empty();

PROOF static thm cm_prove_target_activate_local_empty(void) {
  term activated =
      `cm_activate_local (p:cm_program) (fid:int) (slot:int)
        (st:cm_src_state)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (slot:int) (st:cm_src_state)
         (ann:cm_annotation) (target:tvm_task).
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         cm_state_tags_generation_below st
           (cm_state_nextgen st) ==>
         0i <
           cm_slot_size (cm_program_structs p)
             (inth slot (cm_function_locals
               (inth fid (cm_program_functions p)))) ==>
         cm_spill_frames_generation_below (cm_state_nextgen st)
           (cm_active_spill_frames fid st ann) ==>
         cm_running_target_sim p fid st [] ann target ==>
         cm_running_target_sim p fid
           (cm_activate_local p fid slot st) [] ann target`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state) [] (ann:cm_annotation) (target:tvm_task)`);
  thm expanded = conv_rule(rewrite_conv(THM_LIST(
      cm_running_target_sim_def)), old_running);
  thm body = assume_rule(
      `(target:tvm_task) == TVMRunTask (cm_compile_model (p:cm_program))
          (vm:tvm_state) &&
       tvm_pc vm == cm_ann_pc (ann:cm_annotation) &&
       cm_machine_state_sim p (st:cm_src_state) vm
         (cm_ann_calls ann) (cm_active_spill_frames (fid:int) st ann)
         [] []`);
  thm machine = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `slot:int`, `st:cm_src_state`,
      `vm:tvm_state`, `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`),
      cm_machine_activate_local_empty);
  machine = match_mp_rule(machine, assume_rule(
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`));
  machine = match_mp_rule(machine, assume_rule(
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`));
  machine = match_mp_rule(machine, assume_rule(
      `0i < ${cm_target_state_local_width():int}`));
  machine = match_mp_rule(machine, assume_rule(
      `cm_spill_frames_generation_below (cm_state_nextgen st)
        (cm_active_spill_frames (fid:int) st (ann:cm_annotation))`));
  machine = match_mp_rule(machine,
      conjunct2_rule(conjunct2_rule(body)));
  thm_list active_rules = get_cm_state_core_defs();
  vector_add(&active_rules, get_cm_activate_local_def());
  vector_add(&active_rules, cm_active_spill_frames_def);
  thm new_active = apply_conversion(reduce_rewrite_conv(active_rules),
      `cm_active_spill_frames (fid:int) ${activated:cm_src_state}
        (ann:cm_annotation)`);
  thm old_active = apply_conversion(reduce_rewrite_conv(active_rules),
      `cm_active_spill_frames (fid:int) (st:cm_src_state)
        (ann:cm_annotation)`);
  thm active_equal = trans_rule(old_active, sym_rule(new_active));
  thm active_lift = beta_norm(ap_term_rule(
      `\frames:(cm_spill_frame)list.
         cm_machine_state_sim (p:cm_program) ${activated:cm_src_state}
           (vm:tvm_state) (cm_ann_calls (ann:cm_annotation))
           frames [] []`,
      active_equal));
  machine = eq_mp_rule(active_lift, machine);
  term exists_body =
      `?next_vm.
         (target:tvm_task) == TVMRunTask (cm_compile_model (p:cm_program))
           (next_vm:tvm_state) &&
         tvm_pc next_vm == cm_ann_pc (ann:cm_annotation) &&
         cm_machine_state_sim p ${activated:cm_src_state} next_vm
           (cm_ann_calls ann)
           (cm_active_spill_frames (fid:int) ${activated:cm_src_state} ann)
           [] []`;
  thm witness = exists_rule(exists_body, `vm:tvm_state`,
      conj_rule(conjunct1_rule(body),
        conj_rule(conjunct1_rule(conjunct2_rule(body)), machine)));
  thm chosen = choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_running_target_sim_def)));
  ACCEPT_TAC(opened, chosen);
  return gnode_prove(root);
}
PROOF thm cm_target_activate_local_empty =
    cm_prove_target_activate_local_empty();

PROOF thm get_cm_target_activate_local_empty(void) {
  return cm_target_activate_local_empty;
}

PROOF static int cmc_preservation_target_state_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_state_axioms_before,
      "cmc_preservation_target_state introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_activate_local_empty)) == 0,
      "local-allocation target transport theorem has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_state_checks =
    cmc_preservation_target_state_final_checks();
