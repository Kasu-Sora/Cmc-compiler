#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_spill.h"
#include "cmc_preservation_spill_safety.h"
#include "cmc_preservation_target_spill_runtime.h"

#require "cmc_preservation_target_spill.c"
#require "cmc_preservation_spill_safety.c"

PROOF static size_t _cmc_preservation_target_spill_runtime_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_target_temp_store_runtime(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (slot:int) (v:cm_value) (values:(cm_value)list)
         (ann:cm_annotation) (target:tvm_task)
         (rest:(tvm_inst)list) (address:int).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (cm_temp_store_code p fid slot ++ rest) ==>
         cm_running_target_sim p fid st (v :: values) ann target ==>
         cm_runtime_stack p (cm_state_regions st) fid (cm_state_fp st)
           (cm_state_regions st) (cm_ann_cursors ann)
           (cm_spill_put slot v (cm_ann_spills ann))
           (cm_ann_saved ann) (cm_ann_calls ann) ==>
         0i <= fid ==>
         ilength values < 65534i ==>
         cm_tagged_span_valid st ==>
         tower_signed64 (cm_state_fp st) ==>
         tower_signed64 (cm_temp_offset p fid slot) ==>
         address == cm_state_fp st + cm_temp_offset p fid slot ==>
         tower_signed64 address ==>
         tower_word_valid address ==>
         cm_running_target_sim p fid st values
           (cm_ann_put_spill slot v
             (cm_ann_linear (cm_temp_store_code p fid slot) ann))
           (tvm_iter 5 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm stack = assume_rule(
      `cm_runtime_stack (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (cm_ann_cursors (ann:cm_annotation))
        (cm_spill_put (slot:int) (v:cm_value)
          (cm_ann_spills ann))
        (cm_ann_saved ann) (cm_ann_calls ann)`);
  thm fid_nonnegative = assume_rule(`0i <= (fid:int)`);
  thm address_equal = assume_rule(
      `(address:int) ==
       cm_state_fp (st:cm_src_state) +
         cm_temp_offset (p:cm_program) (fid:int) (slot:int)`);
  thm metadata = specl_rule(TERM_LIST(
      `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
      `cm_ann_cursors (ann:cm_annotation)`, `fid:int`,
      `cm_state_fp (st:cm_src_state)`, `cm_state_regions st`,
      `cm_ann_spills (ann:cm_annotation)`,
      `cm_ann_saved (ann:cm_annotation)`,
      `cm_ann_calls (ann:cm_annotation)`, `slot:int`,
      `v:cm_value`, `address:int`),
      get_cm_runtime_spill_metadata_safe());
  metadata = match_mp_rule(metadata, stack);
  metadata = match_mp_rule(metadata, fid_nonnegative);
  metadata = match_mp_rule(metadata, address_equal);
  thm outside = specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`,
      `cm_ann_cursors (ann:cm_annotation)`, `fid:int`,
      `cm_state_fp (st:cm_src_state)`,
      `cm_ann_spills (ann:cm_annotation)`,
      `cm_ann_saved (ann:cm_annotation)`,
      `cm_ann_calls (ann:cm_annotation)`, `slot:int`,
      `v:cm_value`, `address:int`),
      get_cm_runtime_spill_outside_live());
  outside = match_mp_rule(outside, stack);
  outside = match_mp_rule(outside, address_equal);
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, `slot:int`,
      `v:cm_value`, `values:(cm_value)list`,
      `ann:cm_annotation`, `target:tvm_task`,
      `rest:(tvm_inst)list`, `address:int`),
      get_cm_target_temp_store());
  result = match_mp_rule(result, assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (cm_temp_store_code p (fid:int) (slot:int) ++
          (rest:(tvm_inst)list))`));
  result = match_mp_rule(result, assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state) ((v:cm_value) :: (values:(cm_value)list))
        (ann:cm_annotation) (target:tvm_task)`));
  result = match_mp_rule(result, assume_rule(
      `ilength (values:(cm_value)list) < 65534i`));
  result = match_mp_rule(result, assume_rule(
      `cm_tagged_span_valid (st:cm_src_state)`));
  result = match_mp_rule(result, outside);
  result = match_mp_rule(result, conjunct1_rule(metadata));
  result = match_mp_rule(result,
      conjunct1_rule(conjunct2_rule(metadata)));
  result = match_mp_rule(result,
      conjunct2_rule(conjunct2_rule(metadata)));
  result = match_mp_rule(result, assume_rule(
      `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  result = match_mp_rule(result, assume_rule(
      `tower_signed64
        (cm_temp_offset (p:cm_program) (fid:int) (slot:int))`));
  result = match_mp_rule(result, address_equal);
  result = match_mp_rule(result, assume_rule(
      `tower_signed64 (address:int)`));
  result = match_mp_rule(result, assume_rule(
      `tower_word_valid (address:int)`));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_target_temp_store_runtime =
    cm_prove_target_temp_store_runtime();

PROOF thm get_cm_target_temp_store_runtime(void) {
  return cm_target_temp_store_runtime;
}

PROOF static int cmc_preservation_target_spill_runtime_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_spill_runtime_axioms_before,
      "cmc_preservation_target_spill_runtime introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_spill_runtime_checks =
    cmc_preservation_target_spill_runtime_final_checks();
