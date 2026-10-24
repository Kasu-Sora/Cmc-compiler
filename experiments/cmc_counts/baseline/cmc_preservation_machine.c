#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_state.h"
#require "cmc_preservation_state.c"
#include "cmc_preservation_machine.h"

PROOF static size_t _cmc_preservation_machine_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_encode_values_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (values:(cm_value)list).
         ilength (cm_encode_values st values) == ilength values`);
  gnode_list cases = INDUCT_TAC(root, `values:(cm_value)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        cm_encode_values_def, get_theorem_by_name("ILENGTH_DEF")));
  }
  return gnode_prove(root);
}
PROOF thm cm_encode_values_length = cm_prove_encode_values_length();

PROOF thm cm_machine_sim_parts = cm_machine_state_sim_def;
PROOF static thm cm_machine_operand_fact(const thm simulation) {
  thm parts = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_machine_state_sim_def)),
      concl(simulation)), simulation);
  for (size_t i = 0; i < 7; ++i) {
    parts = conjunct2_rule(parts);
  }
  return conv_rule(
      rewrite_conv(THM_LIST(cm_operand_suffix_sim_def)), parts);
}

PROOF static thm cm_prove_machine_sim_restack(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (old_values:(cm_value)list) (new_values:(cm_value)list)
         (suffix:(int)list) (pc:int) (new_stack:(int)list).
         cm_machine_state_sim p st target frames spill_frames
           old_values suffix ==>
         new_stack == cm_encode_values st new_values ++ suffix ==>
         cm_machine_state_sim p st
           (TVMState pc new_stack (tvm_calls target) (tvm_mem target)
             (tvm_input target) (tvm_output target))
           frames spill_frames new_values suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm source = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (old_values:(cm_value)list) (suffix:(int)list)`);
  thm parts = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_machine_state_sim_def)), concl(source)),
      source);
  thm initialized = conjunct1_rule(parts);
  parts = conjunct2_rule(parts);
  thm provenance = conjunct1_rule(parts);
  parts = conjunct2_rule(parts);
  thm frame_pointer = conjunct1_rule(parts);
  parts = conjunct2_rule(parts);
  thm calls = conjunct1_rule(parts);
  parts = conjunct2_rule(parts);
  thm spills = conjunct1_rule(parts);
  parts = conjunct2_rule(parts);
  thm input = conjunct1_rule(parts);
  parts = conjunct2_rule(parts);
  thm output = conjunct1_rule(parts);
  thm stack = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_operand_suffix_sim_def)),
      `cm_operand_suffix_sim (st:cm_src_state)
         (new_values:(cm_value)list) (suffix:(int)list)
         (new_stack:(int)list)`)),
      assume_rule(
        `(new_stack:(int)list) ==
           cm_encode_values (st:cm_src_state)
             (new_values:(cm_value)list) ++ (suffix:(int)list)`));
  thm combined = conj_rule(initialized,
      conj_rule(provenance,
      conj_rule(frame_pointer,
      conj_rule(calls,
      conj_rule(spills,
      conj_rule(input,
      conj_rule(output, stack)))))));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_machine_state_sim_def, get_tvm_state_selectors_def())));
  ACCEPT_TAC(opened, combined);
  return gnode_prove(root);
}
PROOF thm cm_machine_sim_restack = cm_prove_machine_sim_restack();

PROOF static thm cm_prove_machine_sim_repc(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (values:(cm_value)list) (suffix:(int)list) (pc:int).
         cm_machine_state_sim p st target frames spill_frames
           values suffix ==>
         cm_machine_state_sim p st
           (TVMState pc (tvm_stack target) (tvm_calls target)
             (tvm_mem target) (tvm_input target) (tvm_output target))
           frames spill_frames values suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (values:(cm_value)list) (suffix:(int)list)`);
  thm parts = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_machine_state_sim_def)),
      concl(simulation)), simulation);
  for (size_t i = 0; i < 7; ++i) {
    parts = conjunct2_rule(parts);
  }
  thm stack = conv_rule(
      rewrite_conv(THM_LIST(cm_operand_suffix_sim_def)), parts);
  thm result = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `values:(cm_value)list`, `values:(cm_value)list`,
      `suffix:(int)list`, `pc:int`,
      `tvm_stack (target:tvm_state)`),
      cm_machine_sim_restack), simulation), stack);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_machine_sim_repc = cm_prove_machine_sim_repc();

PROOF static thm cm_prove_machine_sim_stack_shape(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (values:(cm_value)list) (suffix:(int)list).
         cm_machine_state_sim p st target frames spill_frames
           values suffix ==>
         tvm_stack target == cm_encode_values st values ++ suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  ACCEPT_TAC(leaf, cm_machine_operand_fact(assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (values:(cm_value)list) (suffix:(int)list)`)));
  return gnode_prove(root);
}
PROOF thm cm_machine_sim_stack_shape =
    cm_prove_machine_sim_stack_shape();

PROOF static thm cm_prove_machine_sim_stack_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (values:(cm_value)list) (suffix:(int)list).
         cm_machine_state_sim p st target frames spill_frames
           values suffix ==>
         ilength (tvm_stack target) ==
           ilength values + ilength suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm stack = cm_machine_operand_fact(assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (values:(cm_value)list) (suffix:(int)list)`));
  thm length = ap_term_rule(`ilength:(int)list->int`, stack);
  ACCEPT_TAC(leaf, conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_encode_values_length,
      get_theorem_by_name("ILENGTH_APPEND"))), length));
  return gnode_prove(root);
}
PROOF thm cm_machine_sim_stack_length =
    cm_prove_machine_sim_stack_length();

PROOF static thm cm_prove_machine_sim_stack_head(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (v:cm_value) (values:(cm_value)list) (suffix:(int)list).
         cm_machine_state_sim p st target frames spill_frames
           (v :: values) suffix ==>
         HD (tvm_stack target) == cm_value_number st v &&
         TL (tvm_stack target) ==
           cm_encode_values st values ++ suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm stack = cm_machine_operand_fact(assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         ((v:cm_value) :: (values:(cm_value)list))
         (suffix:(int)list)`));
  thm normalized = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_encode_values_def, get_theorem_by_name("APPEND"))), stack);
  thm head = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("HD"))),
      ap_term_rule(`HD:(int)list->int`, normalized));
  thm tail = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("TL"))),
      ap_term_rule(`TL:(int)list->(int)list`, normalized));
  ACCEPT_TAC(leaf, conj_rule(head, tail));
  return gnode_prove(root);
}
PROOF thm cm_machine_sim_stack_head =
    cm_prove_machine_sim_stack_head();

PROOF thm get_cm_encode_values_length(void) {
  return cm_encode_values_length;
}
PROOF thm get_cm_machine_sim_parts(void) {
  return cm_machine_sim_parts;
}
PROOF thm get_cm_machine_sim_restack(void) {
  return cm_machine_sim_restack;
}
PROOF thm get_cm_machine_sim_repc(void) {
  return cm_machine_sim_repc;
}
PROOF thm get_cm_machine_sim_stack_length(void) {
  return cm_machine_sim_stack_length;
}
PROOF thm get_cm_machine_sim_stack_shape(void) {
  return cm_machine_sim_stack_shape;
}
PROOF thm get_cm_machine_sim_stack_head(void) {
  return cm_machine_sim_stack_head;
}

PROOF static int cmc_preservation_machine_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_machine_axioms_before,
      "cmc_preservation_machine introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_machine_checks =
    cmc_preservation_machine_final_checks();
