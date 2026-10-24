#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_machine_stack.h"
#require "cmc_preservation_machine_stack.c"
#include "cmc_preservation_machine_ops.h"

PROOF static size_t _cmc_preservation_machine_ops_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_machine_unary_operation(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (arg:cm_value) (values:(cm_value)list) (suffix:(int)list)
         (result:cm_value) (operation:int->int).
         cm_machine_state_sim p st target frames spill_frames
           (arg :: values) suffix ==>
         operation (cm_value_number st arg) ==
           cm_value_number st result ==>
         cm_machine_state_sim p st
           (tvm_next_state target
             (operation (HD (tvm_stack target)) ::
              TL (tvm_stack target))
             (tvm_calls target) (tvm_mem target)
             (tvm_input target) (tvm_output target))
           frames spill_frames (result :: values) suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         ((arg:cm_value) :: (values:(cm_value)list))
         (suffix:(int)list)`);
  thm shape = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `(arg:cm_value) :: (values:(cm_value)list)`,
      `suffix:(int)list`), cm_machine_sim_stack_shape), simulation);
  thm stack = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        shape, assume_rule(
          `(operation:int->int)
             (cm_value_number (st:cm_src_state) (arg:cm_value)) ==
           cm_value_number st (result:cm_value)`),
        cm_encode_values_def, get_theorem_by_name("APPEND"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
      `(operation:int->int) (HD (tvm_stack (target:tvm_state))) ::
         TL (tvm_stack target) ==
       cm_encode_values (st:cm_src_state)
         ((result:cm_value) :: (values:(cm_value)list)) ++
       (suffix:(int)list)`));
  thm result_sim = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `(arg:cm_value) :: (values:(cm_value)list)`,
      `(result:cm_value) :: values`, `suffix:(int)list`,
      `tvm_pc (target:tvm_state) + 1i`,
      `(operation:int->int) (HD (tvm_stack target)) ::
       TL (tvm_stack target)`), cm_machine_sim_restack),
      simulation), stack);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(get_tvm_next_state_def())));
  ACCEPT_TAC(opened, result_sim);
  return gnode_prove(root);
}
PROOF thm cm_machine_unary_operation =
    cm_prove_machine_unary_operation();

PROOF static thm cm_prove_machine_binary_operation(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (right:cm_value) (left:cm_value)
         (values:(cm_value)list) (suffix:(int)list)
         (result:cm_value) (operation:int->int->int).
         cm_machine_state_sim p st target frames spill_frames
           (right :: left :: values) suffix ==>
         operation (cm_value_number st left)
             (cm_value_number st right) ==
           cm_value_number st result ==>
         cm_machine_state_sim p st
           (tvm_next_state target
             (operation (HD (TL (tvm_stack target)))
                (HD (tvm_stack target)) ::
              TL (TL (tvm_stack target)))
             (tvm_calls target) (tvm_mem target)
             (tvm_input target) (tvm_output target))
           frames spill_frames (result :: values) suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         ((right:cm_value) :: (left:cm_value) ::
           (values:(cm_value)list)) (suffix:(int)list)`);
  thm shape = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `(right:cm_value) :: (left:cm_value) ::
        (values:(cm_value)list)`, `suffix:(int)list`),
      cm_machine_sim_stack_shape), simulation);
  thm stack = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        shape, assume_rule(
          `(operation:int->int->int)
             (cm_value_number (st:cm_src_state) (left:cm_value))
             (cm_value_number st (right:cm_value)) ==
           cm_value_number st (result:cm_value)`),
        cm_encode_values_def, get_theorem_by_name("APPEND"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
      `(operation:int->int->int)
          (HD (TL (tvm_stack (target:tvm_state))))
          (HD (tvm_stack target)) :: TL (TL (tvm_stack target)) ==
       cm_encode_values (st:cm_src_state)
         ((result:cm_value) :: (values:(cm_value)list)) ++
       (suffix:(int)list)`));
  thm result_sim = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `(right:cm_value) :: (left:cm_value) ::
        (values:(cm_value)list)`,
      `(result:cm_value) :: values`, `suffix:(int)list`,
      `tvm_pc (target:tvm_state) + 1i`,
      `(operation:int->int->int)
         (HD (TL (tvm_stack target))) (HD (tvm_stack target)) ::
       TL (TL (tvm_stack target))`), cm_machine_sim_restack),
      simulation), stack);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(get_tvm_next_state_def())));
  ACCEPT_TAC(opened, result_sim);
  return gnode_prove(root);
}
PROOF thm cm_machine_binary_operation =
    cm_prove_machine_binary_operation();

PROOF static thm cm_prove_machine_jump(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (values:(cm_value)list) (suffix:(int)list) (pc:int).
         cm_machine_state_sim p st target frames spill_frames
           values suffix ==>
         cm_machine_state_sim p st
           (tvm_jump_state target pc (tvm_stack target)
             (tvm_calls target) (tvm_mem target)
             (tvm_input target) (tvm_output target))
           frames spill_frames values suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (values:(cm_value)list) (suffix:(int)list)`);
  thm result = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `values:(cm_value)list`, `suffix:(int)list`, `pc:int`),
      cm_machine_sim_repc), simulation);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(get_tvm_jump_state_def())));
  ACCEPT_TAC(opened, result);
  return gnode_prove(root);
}
PROOF thm cm_machine_jump = cm_prove_machine_jump();

PROOF static thm cm_prove_machine_branch_pop(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (condition:cm_value) (values:(cm_value)list)
         (suffix:(int)list) (pc:int).
         cm_machine_state_sim p st target frames spill_frames
           (condition :: values) suffix ==>
         cm_machine_state_sim p st
           (TVMState pc (TL (tvm_stack target)) (tvm_calls target)
             (tvm_mem target) (tvm_input target) (tvm_output target))
           frames spill_frames values suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         ((condition:cm_value) :: (values:(cm_value)list))
         (suffix:(int)list)`);
  thm head = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`, `condition:cm_value`,
      `values:(cm_value)list`, `suffix:(int)list`),
      cm_machine_sim_stack_head), simulation);
  ACCEPT_TAC(leaf, mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `(condition:cm_value) :: (values:(cm_value)list)`,
      `values:(cm_value)list`, `suffix:(int)list`, `pc:int`,
      `TL (tvm_stack (target:tvm_state))`),
      cm_machine_sim_restack), simulation), conjunct2_rule(head)));
  return gnode_prove(root);
}
PROOF thm cm_machine_branch_pop = cm_prove_machine_branch_pop();

PROOF thm get_cm_machine_unary_operation(void) {
  return cm_machine_unary_operation;
}
PROOF thm get_cm_machine_binary_operation(void) {
  return cm_machine_binary_operation;
}
PROOF thm get_cm_machine_jump(void) { return cm_machine_jump; }
PROOF thm get_cm_machine_branch_pop(void) {
  return cm_machine_branch_pop;
}

PROOF static int cmc_preservation_machine_ops_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_machine_ops_axioms_before,
      "cmc_preservation_machine_ops introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_machine_ops_checks =
    cmc_preservation_machine_ops_final_checks();
