#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_call_setup.h"

#require "cmc_preservation_target_call_frame.c"

PROOF static size_t _cmc_preservation_target_call_setup_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_call_frame_save_code_def = new_fun_definition(
    `cm_call_frame_save_code (frame_size:int) : (tvm_inst)list =
       [TVMInst TVMPushOp 8i;
        TVMInst TVMLoadOp 0i;
        TVMInst TVMDupOp 0i;
        TVMInst TVMPushOp frame_size;
        TVMInst TVMSubOp 0i;
        TVMInst TVMStoreOp 0i]`);

PROOF thm cm_ann_after_call_frame_save_def = new_fun_definition(
    `cm_ann_after_call_frame_save (frame_size:int) (base:int)
       (ann:cm_annotation) : cm_annotation =
       cm_ann_call_rebase base
         (cm_ann_linear [TVMInst TVMStoreOp 0i]
           (cm_ann_linear [TVMInst TVMSubOp 0i]
             (cm_ann_linear (cm_push_code frame_size)
               (cm_ann_linear [TVMInst TVMDupOp 0i]
                 (cm_ann_linear [TVMInst TVMLoadOp 0i]
                   (cm_ann_linear (cm_push_code 8i) ann))))))`);

PROOF static thm cm_call_setup_code_suffix(
    const thm current_code, const term code,
    const term current_ann, const term prefix,
    const term suffix, const term next_ann,
    const thm_list rules) {
  thm current_normal =
      conv_rule(reduce_rewrite_conv(rules), current_code);
  thm tail_rule = ispecl_rule(TERM_LIST(
      code, `cm_ann_pc ${current_ann:cm_annotation}`,
      prefix, suffix), get_cm_code_at_append_right());
  thm tail_raw = mp_rule(
      conv_rule(reduce_rewrite_conv(rules), tail_rule),
      current_normal);
  thm tail_normal =
      conv_rule(reduce_rewrite_conv(rules), tail_raw);
  thm tail_view = apply_conversion(
      reduce_rewrite_conv(rules),
      `cm_code_at ${code:(tvm_inst)list}
        (cm_ann_pc ${next_ann:cm_annotation})
        ${suffix:(tvm_inst)list}`);
  return eq_mp_rule(sym_rule(tail_view), tail_normal);
}

PROOF static thm cm_prove_target_call_frame_save(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (frame_size:int) (base:int) (values:(cm_value)list)
         (ann:cm_annotation) (target:tvm_task)
         (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (cm_call_frame_save_code frame_size ++ rest) ==>
         cm_running_target_sim p fid st values ann target ==>
         ilength values < 65534i ==>
         ~(cm_ann_calls ann == []) ==>
         cm_call_sim_base (HD (cm_ann_calls ann)) == 8i ==>
         cm_call_sim_saved (HD (cm_ann_calls ann)) ==
           cm_state_fp st ==>
         cm_tagged_span_valid st ==>
         (!addr.
            cm_live_address st addr ==>
            ~(base <= addr && addr < base + 8i)) ==>
         cm_range_disjoint base 8i 8i 8i ==>
         cm_call_frames_store_safe CMIntTy base
           (TL (cm_ann_calls ann)) ==>
         cm_spill_frames_store_safe p CMIntTy base
           (cm_active_spill_frames fid st ann) ==>
         tower_signed64 (cm_state_fp st) ==>
         tower_signed64 frame_size ==>
         base == cm_state_fp st - frame_size ==>
         tower_signed64 base ==>
         tower_word_valid base ==>
         cm_running_target_sim p fid st values
           (cm_ann_after_call_frame_save frame_size base ann)
           (tvm_iter 6 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);

  term code = `cm_model_code (p:cm_program)`;
  term push8 = `TVMInst TVMPushOp 8i`;
  term load = `TVMInst TVMLoadOp 0i`;
  term dup = `TVMInst TVMDupOp 0i`;
  term push_frame = `TVMInst TVMPushOp (frame_size:int)`;
  term sub = `TVMInst TVMSubOp 0i`;
  term store = `TVMInst TVMStoreOp 0i`;
  term suffix1 =
      `${load:tvm_inst} :: ${dup:tvm_inst} ::
       ${push_frame:tvm_inst} :: ${sub:tvm_inst} ::
       ${store:tvm_inst} :: (rest:(tvm_inst)list)`;
  term suffix2 =
      `${dup:tvm_inst} :: ${push_frame:tvm_inst} ::
       ${sub:tvm_inst} :: ${store:tvm_inst} ::
       (rest:(tvm_inst)list)`;
  term suffix3 =
      `${push_frame:tvm_inst} :: ${sub:tvm_inst} ::
       ${store:tvm_inst} :: (rest:(tvm_inst)list)`;
  term suffix4 =
      `${sub:tvm_inst} :: ${store:tvm_inst} ::
       (rest:(tvm_inst)list)`;
  term suffix5 =
      `${store:tvm_inst} :: (rest:(tvm_inst)list)`;

  term ann1 =
      `cm_ann_linear (cm_push_code 8i) (ann:cm_annotation)`;
  term ann2 =
      `cm_ann_linear [TVMInst TVMLoadOp 0i] ${ann1:cm_annotation}`;
  term ann3 =
      `cm_ann_linear [TVMInst TVMDupOp 0i] ${ann2:cm_annotation}`;
  term ann4 =
      `cm_ann_linear (cm_push_code (frame_size:int))
        ${ann3:cm_annotation}`;
  term ann5 =
      `cm_ann_linear [TVMInst TVMSubOp 0i] ${ann4:cm_annotation}`;
  term ann6 =
      `cm_ann_call_rebase (base:int)
        (cm_ann_linear [TVMInst TVMStoreOp 0i]
          ${ann5:cm_annotation})`;

  thm_list rules = THM_LIST(
      cm_call_frame_save_code_def, get_cm_push_code_def(),
      cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_pc_def, cm_ann_temp_def,
      cm_ann_break_def, cm_ann_continue_def,
      cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def,
      cm_active_spill_frames_def,
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("ILENGTH_DEF"));
  thm code0 = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (cm_call_frame_save_code (frame_size:int) ++
          (rest:(tvm_inst)list))`);
  code0 = conv_rule(reduce_rewrite_conv(rules), code0);
  thm code1 = cm_call_setup_code_suffix(
      code0, code, `ann:cm_annotation`,
      `[${push8:tvm_inst}]:(tvm_inst)list`, suffix1, ann1, rules);
  thm code2 = cm_call_setup_code_suffix(
      code1, code, ann1,
      `[${load:tvm_inst}]:(tvm_inst)list`, suffix2, ann2, rules);
  thm code3 = cm_call_setup_code_suffix(
      code2, code, ann2,
      `[${dup:tvm_inst}]:(tvm_inst)list`, suffix3, ann3, rules);
  thm code4 = cm_call_setup_code_suffix(
      code3, code, ann3,
      `[${push_frame:tvm_inst}]:(tvm_inst)list`, suffix4, ann4, rules);
  thm code5 = cm_call_setup_code_suffix(
      code4, code, ann4,
      `[${sub:tvm_inst}]:(tvm_inst)list`, suffix5, ann5, rules);

  thm capacity = assume_rule(
      `ilength (values:(cm_value)list) < 65534i`);
  thm capacity0 = mp_rule(int_arith_rule(
      `ilength (values:(cm_value)list) < 65534i ==>
       ilength values < 65536i`), capacity);
  thm capacity1_raw = mp_rule(int_arith_rule(
      `ilength (values:(cm_value)list) < 65534i ==>
       1i + ilength values < 65536i`), capacity);
  thm capacity1_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
      `ilength
        (CMIntV (cm_state_fp (st:cm_src_state)) ::
          (values:(cm_value)list)) < 65536i`);
  thm capacity1 = eq_mp_rule(sym_rule(capacity1_view), capacity1_raw);
  thm capacity2_raw = mp_rule(int_arith_rule(
      `ilength (values:(cm_value)list) < 65534i ==>
       1i + 1i + ilength values < 65536i`), capacity);
  thm capacity2_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
      `ilength
        (CMIntV (cm_state_fp (st:cm_src_state)) ::
         CMIntV (cm_state_fp st) :: values) < 65536i`);
  thm capacity2 = eq_mp_rule(sym_rule(capacity2_view), capacity2_raw);

  thm push8_bridge = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_value_number_def(), get_tower_wrap64_def())),
      `tower_wrap64 8i ==
       cm_value_number (st:cm_src_state) (CMIntV 8i)`));
  thm push_frame_bridge = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_value_number_def())),
      `tower_wrap64 (frame_size:int) ==
       cm_value_number (st:cm_src_state) (CMIntV frame_size)`));

  thm sim0 = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state) (values:(cm_value)list)
        (ann:cm_annotation) (target:tvm_task)`);
  thm sim1 = match_mp_rule(match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `values:(cm_value)list`, `ann:cm_annotation`,
        `target:tvm_task`, `CMIntV 8i:cm_value`, `8i:int`, suffix1),
        get_cm_target_push()), code0), sim0), capacity0), push8_bridge);
  thm sim2 = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `values:(cm_value)list`, ann1,
        `tvm_iter 1 (target:tvm_task)`, suffix2),
        get_cm_target_load_fp()), code1), sim1),
      assume_rule(`tower_signed64 (cm_state_fp (st:cm_src_state))`));
  thm sim3 = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `CMIntV (cm_state_fp (st:cm_src_state)):cm_value`,
        `values:(cm_value)list`, ann2,
        `tvm_iter 1 (tvm_iter 1 (target:tvm_task))`, suffix3),
        get_cm_target_dup()), code2), sim2), capacity1);
  thm sim4 = match_mp_rule(match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `CMIntV (cm_state_fp (st:cm_src_state)) ::
          CMIntV (cm_state_fp st) :: (values:(cm_value)list)`,
        ann3,
        `tvm_iter 1 (tvm_iter 1 (tvm_iter 1 (target:tvm_task)))`,
        `CMIntV (frame_size:int):cm_value`, `frame_size:int`, suffix4),
        get_cm_target_push()), code3), sim3), capacity2),
      push_frame_bridge);

  thm fp_fixed = mp_rule(spec_rule(
      `cm_state_fp (st:cm_src_state)`, get_tower_wrap64_fixed()),
      assume_rule(`tower_signed64 (cm_state_fp (st:cm_src_state))`));
  thm frame_fixed = mp_rule(spec_rule(
      `frame_size:int`, get_tower_wrap64_fixed()),
      assume_rule(`tower_signed64 (frame_size:int)`));
  thm base_equal = assume_rule(
      `(base:int) == cm_state_fp (st:cm_src_state) - frame_size`);
  thm difference_signed = conv_rule(
      rewrite_conv(THM_LIST(base_equal)),
      assume_rule(`tower_signed64 (base:int)`));
  thm difference_fixed = mp_rule(spec_rule(
      `cm_state_fp (st:cm_src_state) - frame_size`,
      get_tower_wrap64_fixed()), difference_signed);
  thm sub_bridge = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_value_number_def(), get_tower_sub_def(),
        fp_fixed, frame_fixed, difference_fixed, base_equal)),
      `tower_sub
         (cm_value_number (st:cm_src_state)
           (CMIntV (cm_state_fp st)))
         (cm_value_number st (CMIntV (frame_size:int))) ==
       cm_value_number st (CMIntV (base:int))`));
  thm sim5 = match_mp_rule(match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `CMIntV (frame_size:int):cm_value`,
        `CMIntV (cm_state_fp (st:cm_src_state)):cm_value`,
        `CMIntV (cm_state_fp (st:cm_src_state)) ::
          (values:(cm_value)list)`,
        ann4,
        `tvm_iter 1 (tvm_iter 1
          (tvm_iter 1 (tvm_iter 1 (target:tvm_task))))`,
        `TVMSubOp:tvm_opcode`, `tower_sub:int->int->int`,
        `CMIntV (base:int):cm_value`, suffix5),
        get_cm_target_binary_total()), get_tvm_sub_transition()),
      code4), sim4), sub_bridge);

  thm code5_ready = conv_rule(reduce_rewrite_conv(rules), code5);
  thm sim5_ready = conv_rule(reduce_rewrite_conv(rules), sim5);
  thm save_rule = conv_rule(reduce_rewrite_conv(rules),
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `base:int`, `values:(cm_value)list`, ann5,
        `tvm_iter 1 (tvm_iter 1 (tvm_iter 1
          (tvm_iter 1 (tvm_iter 1 (target:tvm_task)))))`,
        `rest:(tvm_inst)list`), get_cm_target_call_save()));
  thm sim6 = match_mp_rule(match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(match_mp_rule(match_mp_rule(match_mp_rule(match_mp_rule(
        save_rule,
        code5_ready), sim5_ready), assume_rule(`~(cm_ann_calls (ann:cm_annotation) == [])`)),
        assume_rule(`cm_call_sim_base (HD (cm_ann_calls ann)) == 8i`)),
        assume_rule(`cm_call_sim_saved (HD (cm_ann_calls ann)) ==
          cm_state_fp (st:cm_src_state)`)),
        assume_rule(`cm_tagged_span_valid (st:cm_src_state)`)),
        assume_rule(`!addr. cm_live_address (st:cm_src_state) addr ==>
          ~((base:int) <= addr && addr < base + 8i)`)),
        assume_rule(`cm_range_disjoint (base:int) 8i 8i 8i`)),
        assume_rule(`cm_call_frames_store_safe CMIntTy (base:int)
          (TL (cm_ann_calls (ann:cm_annotation)))`)),
        conv_rule(reduce_rewrite_conv(rules),
          assume_rule(`cm_spill_frames_store_safe (p:cm_program) CMIntTy
            (base:int) (cm_active_spill_frames (fid:int) st ann)`))),
        assume_rule(`tower_signed64 (cm_state_fp (st:cm_src_state))`)),
        assume_rule(`tower_signed64 (base:int)`)),
        assume_rule(`tower_word_valid (base:int)`));

  term desired =
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state) (values:(cm_value)list)
        (cm_ann_after_call_frame_save (frame_size:int) (base:int)
          (ann:cm_annotation))
        (tvm_iter 6 (target:tvm_task))`;
  thm_list final_rules = THM_LIST(
      cm_ann_after_call_frame_save_def,
      cm_ann_call_rebase_def, cm_rebase_call_frames_def,
      cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_pc_def, cm_ann_temp_def,
      cm_ann_break_def, cm_ann_continue_def,
      cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def,
      get_cm_push_code_def(), get_theorem_by_name("ILENGTH_DEF"));
  vector_add(&final_rules, conjunct1_rule(get_tvm_iter_def()));
  term iter_index = `0`;
  for (size_t index = 0; index < 6; ++index) {
    thm successor = apply_conversion(
        get_conversion_by_name("NUM_SUC_CONV"),
        mk_comb(`SUC`, iter_index));
    vector_add(&final_rules, conv_rule(
        rewrite_conv(THM_LIST(successor)),
        spec_rule(iter_index, conjunct2_rule(get_tvm_iter_def()))));
    iter_index = rhs_of(successor);
  }
  thm normalized =
      conv_rule(reduce_rewrite_conv(final_rules), sim6);
  thm reduction = apply_conversion(
      reduce_rewrite_conv(final_rules), desired);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(reduction), normalized));
  return gnode_prove(root);
}
PROOF thm cm_target_call_frame_save =
    cm_prove_target_call_frame_save();

PROOF thm get_cm_call_frame_save_code_def(void) {
  return cm_call_frame_save_code_def;
}
PROOF thm get_cm_ann_after_call_frame_save_def(void) {
  return cm_ann_after_call_frame_save_def;
}
PROOF thm get_cm_target_call_frame_save(void) {
  return cm_target_call_frame_save;
}

PROOF static int cmc_preservation_target_call_setup_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_call_setup_axioms_before,
      "cmc_preservation_target_call_setup introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_call_setup_checks =
    cmc_preservation_target_call_setup_final_checks();
