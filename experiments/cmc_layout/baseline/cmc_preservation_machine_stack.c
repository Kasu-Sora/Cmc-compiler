#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_machine.h"
#require "cmc_preservation_machine.c"
#include "cmc_preservation_machine_stack.h"

PROOF static size_t _cmc_preservation_machine_stack_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_machine_push(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (values:(cm_value)list) (suffix:(int)list)
         (v:cm_value) (imm:int).
         cm_machine_state_sim p st target frames spill_frames
           values suffix ==>
         tower_wrap64 imm == cm_value_number st v ==>
         cm_machine_state_sim p st
           (tvm_next_state target
             (tower_wrap64 imm :: tvm_stack target)
             (tvm_calls target) (tvm_mem target)
             (tvm_input target) (tvm_output target))
           frames spill_frames (v :: values) suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (values:(cm_value)list) (suffix:(int)list)`);
  thm shape = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `values:(cm_value)list`, `suffix:(int)list`),
      cm_machine_sim_stack_shape), simulation);
  thm stack = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        shape, assume_rule(
          `tower_wrap64 (imm:int) ==
           cm_value_number (st:cm_src_state) (v:cm_value)`),
        cm_encode_values_def, get_theorem_by_name("APPEND"))),
      `tower_wrap64 (imm:int) :: tvm_stack (target:tvm_state) ==
       cm_encode_values (st:cm_src_state)
         ((v:cm_value) :: (values:(cm_value)list)) ++
       (suffix:(int)list)`));
  thm result = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `values:(cm_value)list`,
      `(v:cm_value) :: (values:(cm_value)list)`,
      `suffix:(int)list`, `tvm_pc (target:tvm_state) + 1i`,
      `tower_wrap64 (imm:int) :: tvm_stack (target:tvm_state)`),
      cm_machine_sim_restack), simulation), stack);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(get_tvm_next_state_def())));
  ACCEPT_TAC(opened, result);
  return gnode_prove(root);
}
PROOF thm cm_machine_push = cm_prove_machine_push();

PROOF static thm cm_prove_machine_pop(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (v:cm_value) (values:(cm_value)list) (suffix:(int)list).
         cm_machine_state_sim p st target frames spill_frames
           (v :: values) suffix ==>
         cm_machine_state_sim p st
           (tvm_next_state target (TL (tvm_stack target))
             (tvm_calls target) (tvm_mem target)
             (tvm_input target) (tvm_output target))
           frames spill_frames values suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         ((v:cm_value) :: (values:(cm_value)list))
         (suffix:(int)list)`);
  thm head = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`, `v:cm_value`,
      `values:(cm_value)list`, `suffix:(int)list`),
      cm_machine_sim_stack_head), simulation);
  thm result = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `(v:cm_value) :: (values:(cm_value)list)`,
      `values:(cm_value)list`, `suffix:(int)list`,
      `tvm_pc (target:tvm_state) + 1i`,
      `TL (tvm_stack (target:tvm_state))`),
      cm_machine_sim_restack), simulation), conjunct2_rule(head));
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(get_tvm_next_state_def())));
  ACCEPT_TAC(opened, result);
  return gnode_prove(root);
}
PROOF thm cm_machine_pop = cm_prove_machine_pop();

PROOF static thm cm_prove_machine_dup(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (v:cm_value) (values:(cm_value)list) (suffix:(int)list).
         cm_machine_state_sim p st target frames spill_frames
           (v :: values) suffix ==>
         cm_machine_state_sim p st
           (tvm_next_state target
             (HD (tvm_stack target) :: tvm_stack target)
             (tvm_calls target) (tvm_mem target)
             (tvm_input target) (tvm_output target))
           frames spill_frames (v :: v :: values) suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         ((v:cm_value) :: (values:(cm_value)list))
         (suffix:(int)list)`);
  thm shape = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `(v:cm_value) :: (values:(cm_value)list)`,
      `suffix:(int)list`), cm_machine_sim_stack_shape), simulation);
  thm head = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`, `v:cm_value`,
      `values:(cm_value)list`, `suffix:(int)list`),
      cm_machine_sim_stack_head), simulation);
  thm stack = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        shape, conjunct1_rule(head), cm_encode_values_def,
        get_theorem_by_name("APPEND"))),
      `HD (tvm_stack (target:tvm_state)) :: tvm_stack target ==
       cm_encode_values (st:cm_src_state)
         ((v:cm_value) :: v :: (values:(cm_value)list)) ++
       (suffix:(int)list)`));
  thm result = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `(v:cm_value) :: (values:(cm_value)list)`,
      `(v:cm_value) :: v :: values`, `suffix:(int)list`,
      `tvm_pc (target:tvm_state) + 1i`,
      `HD (tvm_stack (target:tvm_state)) :: tvm_stack target`),
      cm_machine_sim_restack), simulation), stack);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(get_tvm_next_state_def())));
  ACCEPT_TAC(opened, result);
  return gnode_prove(root);
}
PROOF thm cm_machine_dup = cm_prove_machine_dup();

PROOF static thm cm_prove_machine_swap(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (first:cm_value) (second:cm_value)
         (values:(cm_value)list) (suffix:(int)list).
         cm_machine_state_sim p st target frames spill_frames
           (first :: second :: values) suffix ==>
         cm_machine_state_sim p st
           (tvm_next_state target
             (HD (TL (tvm_stack target)) ::
              HD (tvm_stack target) :: TL (TL (tvm_stack target)))
             (tvm_calls target) (tvm_mem target)
             (tvm_input target) (tvm_output target))
           frames spill_frames (second :: first :: values) suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         ((first:cm_value) :: (second:cm_value) ::
           (values:(cm_value)list)) (suffix:(int)list)`);
  thm shape = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `(first:cm_value) :: (second:cm_value) ::
        (values:(cm_value)list)`, `suffix:(int)list`),
      cm_machine_sim_stack_shape), simulation);
  thm stack = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        shape, cm_encode_values_def, get_theorem_by_name("APPEND"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
      `HD (TL (tvm_stack (target:tvm_state))) ::
         HD (tvm_stack target) :: TL (TL (tvm_stack target)) ==
       cm_encode_values (st:cm_src_state)
         ((second:cm_value) :: (first:cm_value) ::
           (values:(cm_value)list)) ++ (suffix:(int)list)`));
  thm result = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `(first:cm_value) :: (second:cm_value) ::
        (values:(cm_value)list)`,
      `(second:cm_value) :: (first:cm_value) :: values`,
      `suffix:(int)list`, `tvm_pc (target:tvm_state) + 1i`,
      `HD (TL (tvm_stack (target:tvm_state))) ::
       HD (tvm_stack target) :: TL (TL (tvm_stack target))`),
      cm_machine_sim_restack), simulation), stack);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(get_tvm_next_state_def())));
  ACCEPT_TAC(opened, result);
  return gnode_prove(root);
}
PROOF thm cm_machine_swap = cm_prove_machine_swap();

PROOF thm get_cm_machine_push(void) { return cm_machine_push; }
PROOF thm get_cm_machine_pop(void) { return cm_machine_pop; }
PROOF thm get_cm_machine_dup(void) { return cm_machine_dup; }
PROOF thm get_cm_machine_swap(void) { return cm_machine_swap; }

PROOF static int cmc_preservation_machine_stack_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_machine_stack_axioms_before,
      "cmc_preservation_machine_stack introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_machine_stack_checks =
    cmc_preservation_machine_stack_final_checks();
