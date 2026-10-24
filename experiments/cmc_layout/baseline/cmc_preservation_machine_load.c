#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_machine_ops.h"
#include "cmc_sim_ops.h"
#require "cmc_preservation_machine_ops.c"
#require "cmc_sim_ops.c"
#include "cmc_preservation_machine_load.h"

PROOF static size_t _cmc_preservation_machine_load_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_machine_load(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (ptr:cm_value) (values:(cm_value)list) (suffix:(int)list)
         (ty:cm_type).
         cm_machine_state_sim p st target frames spill_frames
           (ptr :: values) suffix ==>
         cm_load_ok ty ptr st ==>
         (ty == CMCharTy || ty == CMIntTy || cm_is_pointer ty) ==>
         cm_live_span st (cm_value_number st ptr)
           (cm_store_width ty) ==>
         cm_machine_state_sim p st
           (tvm_next_state target
             ((if ty == CMCharTy
               then tower_getb (tvm_mem target)
                 (HD (tvm_stack target))
               else tower_getw (tvm_mem target)
                 (HD (tvm_stack target))) ::
              TL (tvm_stack target))
             (tvm_calls target) (tvm_mem target)
             (tvm_input target) (tvm_output target))
           frames spill_frames ((cm_load_value ty ptr st) :: values)
           suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         ((ptr:cm_value) :: (values:(cm_value)list))
         (suffix:(int)list)`);
  thm parts = conv_rule(rewrite_conv(THM_LIST(cm_machine_sim_parts)),
      simulation);
  thm initialized = conjunct1_rule(parts);
  thm provenance = conjunct1_rule(conjunct2_rule(parts));
  thm bridge = mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(
      specl_rule(TERM_LIST(
        `ty:cm_type`, `ptr:cm_value`, `st:cm_src_state`,
        `tvm_mem (target:tvm_state)`),
        get_cm_load_value_number_bridge()),
      assume_rule(`cm_load_ok (ty:cm_type) (ptr:cm_value)
        (st:cm_src_state)`)),
      assume_rule(`(ty:cm_type) == CMCharTy ||
        ty == CMIntTy || cm_is_pointer ty`)), initialized), provenance),
      assume_rule(
        `cm_live_span (st:cm_src_state)
           (cm_value_number st (ptr:cm_value))
           (cm_store_width (ty:cm_type))`));
  thm operation = sym_rule(bridge);
  thm load_effect = beta_norm(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`, `ptr:cm_value`,
      `values:(cm_value)list`, `suffix:(int)list`,
      `cm_load_value (ty:cm_type) (ptr:cm_value) (st:cm_src_state)`,
      `(\addr:int.
         if (ty:cm_type) == CMCharTy
         then tower_getb (tvm_mem (target:tvm_state)) addr
         else tower_getw (tvm_mem target) addr)`),
      cm_machine_unary_operation));
  ACCEPT_TAC(leaf, mp_rule(mp_rule(load_effect, simulation), operation));
  return gnode_prove(root);
}
PROOF thm cm_machine_load = cm_prove_machine_load();

PROOF static thm cm_prove_machine_load_fp(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (values:(cm_value)list) (suffix:(int)list).
         cm_machine_state_sim p st target frames spill_frames
           (CMIntV 8i :: values) suffix ==>
         tower_signed64 (cm_state_fp st) ==>
         cm_machine_state_sim p st
           (tvm_next_state target
             (tower_getw (tvm_mem target)
                (HD (tvm_stack target)) ::
              TL (tvm_stack target))
             (tvm_calls target) (tvm_mem target)
             (tvm_input target) (tvm_output target))
           frames spill_frames
           (CMIntV (cm_state_fp st) :: values) suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
        (target:tvm_state) (frames:(cm_call_sim_frame)list)
        (spill_frames:(cm_spill_frame)list)
        (CMIntV 8i :: (values:(cm_value)list))
        (suffix:(int)list)`);
  thm parts = conv_rule(rewrite_conv(THM_LIST(
      cm_machine_sim_parts)), simulation);
  thm frame_pointer =
      conjunct1_rule(conjunct2_rule(conjunct2_rule(parts)));
  thm fixed = mp_rule(spec_rule(
      `cm_state_fp (st:cm_src_state)`,
      get_tower_wrap64_fixed()), assume_rule(
        `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  thm operation_reduction = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_value_number_def(), get_tower_wrap64_def(), fixed)),
      `tower_getw (tvm_mem (target:tvm_state))
          (cm_value_number (st:cm_src_state) (CMIntV 8i)) ==
       cm_value_number st (CMIntV (cm_state_fp st))`);
  thm operation = eq_mp_rule(
      sym_rule(operation_reduction), frame_pointer);
  thm load_effect = beta_norm(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`, `CMIntV 8i`,
      `values:(cm_value)list`, `suffix:(int)list`,
      `CMIntV (cm_state_fp (st:cm_src_state))`,
      `(\addr:int. tower_getw
          (tvm_mem (target:tvm_state)) addr)`),
      cm_machine_unary_operation));
  ACCEPT_TAC(leaf,
      mp_rule(mp_rule(load_effect, simulation), operation));
  return gnode_prove(root);
}
PROOF thm cm_machine_load_fp = cm_prove_machine_load_fp();

PROOF static thm cm_prove_spill_list_sim_holds(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (mem:int->int)
         (fid:int) (fp:int) (spills:(cm_spill)list)
         (slot:int) (spill_value:cm_value).
         cm_spill_list_sim p st mem fid fp spills ==>
         cm_spill_holds slot spill_value spills ==>
         tower_getw mem (fp + cm_temp_offset p fid slot) ==
           cm_value_number st spill_value`);
  gnode_list cases = INDUCT_TAC(root, `spills:(cm_spill)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_spill_holds_def)), assume_rule(
          `cm_spill_holds (slot:int) (spill_value:cm_value)
            ([]:(cm_spill)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm sim = assume_rule(
        `cm_spill_list_sim (p:cm_program) (st:cm_src_state)
          (mem:int->int) (fid:int) (fp:int)
          ((a0:cm_spill) :: (a1:(cm_spill)list))`);
    thm holds = assume_rule(
        `cm_spill_holds (slot:int) (spill_value:cm_value)
          ((a0:cm_spill) :: (a1:(cm_spill)list))`);
    thm opened_sim = conv_rule(rewrite_conv(THM_LIST(
        cm_spill_list_sim_def)), sim);
    gnode_list slot_cases = BOOL_CASES_TAC(
        leaf, `cm_spill_slot (a0:cm_spill) == (slot:int)`,
        "Hslot");
    {
      thm slot_equal = assume_rule(
          `cm_spill_slot (a0:cm_spill) == (slot:int)`);
      thm value_equal = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_spill_holds_def, slot_equal)), holds);
      thm result = conv_rule(rewrite_conv(THM_LIST(
          slot_equal, value_equal)), conjunct1_rule(opened_sim));
      ACCEPT_TAC(slot_cases[0], result);
    }
    {
      thm slot_different = assume_rule(
          `~(cm_spill_slot (a0:cm_spill) == (slot:int))`);
      thm tail_holds = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_spill_holds_def, slot_different)), holds);
      thm ih =
          assume_rule(goal_lasmps(slot_cases[1]->g)[0].tm);
      thm result = match_mp_rule(match_mp_rule(
          ih, conjunct2_rule(opened_sim)), tail_holds);
      ACCEPT_TAC(slot_cases[1], result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_spill_list_sim_holds =
    cm_prove_spill_list_sim_holds();

PROOF static thm cm_prove_machine_spill_load(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list) (fid:int) (fp:int)
         (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (slot:int) (spill_value:cm_value) (address:int)
         (values:(cm_value)list) (suffix:(int)list).
         cm_machine_state_sim p st target frames
           (CMSpillFrame fid fp spills :: saved)
           (CMIntV address :: values) suffix ==>
         cm_spill_holds slot spill_value spills ==>
         address == fp + cm_temp_offset p fid slot ==>
         tower_signed64 address ==>
         cm_machine_state_sim p st
           (tvm_next_state target
             (tower_getw (tvm_mem target)
                (HD (tvm_stack target)) ::
              TL (tvm_stack target))
             (tvm_calls target) (tvm_mem target)
             (tvm_input target) (tvm_output target))
           frames (CMSpillFrame fid fp spills :: saved)
           (spill_value :: values) suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
        (target:tvm_state) (frames:(cm_call_sim_frame)list)
        (CMSpillFrame (fid:int) (fp:int) (spills:(cm_spill)list) ::
          (saved:(cm_spill_frame)list))
        (CMIntV (address:int) :: (values:(cm_value)list))
        (suffix:(int)list)`);
  thm parts = conv_rule(rewrite_conv(THM_LIST(
      cm_machine_sim_parts)), simulation);
  thm spill_frames = conjunct1_rule(conjunct2_rule(
      conjunct2_rule(conjunct2_rule(conjunct2_rule(parts)))));
  thm spill_list = conjunct1_rule(conv_rule(
      rewrite_conv(THM_LIST(
        cm_spill_frames_sim_def, cm_spill_frame_fid_def,
        cm_spill_frame_fp_def, cm_spill_frame_spills_def)),
      spill_frames));
  thm stored = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `tvm_mem (target:tvm_state)`,
      `fid:int`, `fp:int`, `spills:(cm_spill)list`,
      `slot:int`, `spill_value:cm_value`),
      cm_spill_list_sim_holds), spill_list),
      assume_rule(
        `cm_spill_holds (slot:int) (spill_value:cm_value)
          (spills:(cm_spill)list)`));
  stored = conv_rule(rewrite_conv(THM_LIST(sym_rule(assume_rule(
      `(address:int) ==
       (fp:int) + cm_temp_offset (p:cm_program) (fid:int)
         (slot:int)`)))), stored);
  thm fixed = mp_rule(spec_rule(
      `address:int`, get_tower_wrap64_fixed()), assume_rule(
        `tower_signed64 (address:int)`));
  thm operation_reduction = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_value_number_def(), fixed)),
      `tower_getw (tvm_mem (target:tvm_state))
          (cm_value_number (st:cm_src_state)
            (CMIntV (address:int))) ==
       cm_value_number st (spill_value:cm_value)`);
  thm operation = eq_mp_rule(
      sym_rule(operation_reduction), stored);
  thm load_effect = beta_norm(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `CMSpillFrame (fid:int) (fp:int)
          (spills:(cm_spill)list) ::
        (saved:(cm_spill_frame)list)`,
      `CMIntV (address:int)`, `values:(cm_value)list`,
      `suffix:(int)list`, `spill_value:cm_value`,
      `(\addr:int. tower_getw
          (tvm_mem (target:tvm_state)) addr)`),
      cm_machine_unary_operation));
  ACCEPT_TAC(leaf,
      mp_rule(mp_rule(load_effect, simulation), operation));
  return gnode_prove(root);
}
PROOF thm cm_machine_spill_load =
    cm_prove_machine_spill_load();

PROOF thm get_cm_machine_load(void) { return cm_machine_load; }
PROOF thm get_cm_machine_load_fp(void) {
  return cm_machine_load_fp;
}
PROOF thm get_cm_machine_spill_load(void) {
  return cm_machine_spill_load;
}

PROOF static int cmc_preservation_machine_load_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_machine_load_axioms_before,
      "cmc_preservation_machine_load introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_machine_load_checks =
    cmc_preservation_machine_load_final_checks();
