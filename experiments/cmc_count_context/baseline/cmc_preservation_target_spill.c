#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_code.h"
#include "cmc_preservation_target_spill.h"

#require "cmc_preservation_code.c"
#require "cmc_preservation_target_machine.c"

PROOF static size_t _cmc_preservation_target_spill_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_target_temp_load(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (slot:int) (spill_value:cm_value) (values:(cm_value)list)
         (ann:cm_annotation) (target:tvm_task)
         (rest:(tvm_inst)list) (address:int).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (cm_temp_load_code p fid slot ++ rest) ==>
         cm_running_target_sim p fid st values ann target ==>
         cm_spill_holds slot spill_value (cm_ann_spills ann) ==>
         ilength values < 65535i ==>
         tower_signed64 (cm_state_fp st) ==>
         tower_signed64 (cm_temp_offset p fid slot) ==>
         address == cm_state_fp st + cm_temp_offset p fid slot ==>
         tower_signed64 address ==>
         tower_word_valid address ==>
         cm_running_target_sim p fid st (spill_value :: values)
           (cm_ann_linear (cm_temp_load_code p fid slot) ann)
           (tvm_iter 5 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term code = `cm_model_code (p:cm_program)`;
  term pc = `cm_ann_pc (ann:cm_annotation)`;
  term offset = `cm_temp_offset (p:cm_program) (fid:int) (slot:int)`;
  term push8 = `TVMInst TVMPushOp 8i`;
  term load = `TVMInst TVMLoadOp 0i`;
  term push_offset = `TVMInst TVMPushOp ${offset:int}`;
  term add = `TVMInst TVMAddOp 0i`;
  term suffix1 =
      `${load:tvm_inst} :: ${push_offset:tvm_inst} ::
       ${add:tvm_inst} :: ${load:tvm_inst} :: (rest:(tvm_inst)list)`;
  term suffix2 =
      `${push_offset:tvm_inst} :: ${add:tvm_inst} ::
       ${load:tvm_inst} :: (rest:(tvm_inst)list)`;
  term suffix3 =
      `${add:tvm_inst} :: ${load:tvm_inst} ::
       (rest:(tvm_inst)list)`;
  term suffix4 = `${load:tvm_inst} :: (rest:(tvm_inst)list)`;
  term ann1 =
      `cm_ann_linear (cm_push_code 8i) (ann:cm_annotation)`;
  term ann2 =
      `cm_ann_linear [TVMInst TVMLoadOp 0i] ${ann1:cm_annotation}`;
  term ann3 =
      `cm_ann_linear (cm_push_code ${offset:int})
        ${ann2:cm_annotation}`;
  term ann4 =
      `cm_ann_linear [TVMInst TVMAddOp 0i]
        ${ann3:cm_annotation}`;

  thm old_code = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (cm_temp_load_code p (fid:int) (slot:int) ++
          (rest:(tvm_inst)list))`);
  thm_list code_rules = THM_LIST(
      get_cm_temp_load_code_def(),
      get_cm_fp_relative_address_code_def(),
      get_cm_push_code_def(), get_theorem_by_name("APPEND"),
      get_theorem_by_name("ILENGTH_DEF"), cm_ann_linear_def,
      cm_ann_plain_def, cm_ann_pc_def, cm_ann_temp_def,
      cm_ann_break_def, cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def);
  thm code0 = conv_rule(reduce_rewrite_conv(code_rules), old_code);

  thm tail1_rule = ispecl_rule(TERM_LIST(
      code, pc, `[${push8:tvm_inst}]:(tvm_inst)list`, suffix1),
      get_cm_code_at_append_right());
  thm code1_raw = mp_rule(
      conv_rule(reduce_rewrite_conv(code_rules), tail1_rule), code0);
  thm code1_normal =
      conv_rule(reduce_rewrite_conv(code_rules), code1_raw);
  thm code1_reduction = apply_conversion(
      reduce_rewrite_conv(code_rules),
      `cm_code_at ${code:(tvm_inst)list}
        (cm_ann_pc ${ann1:cm_annotation}) ${suffix1:(tvm_inst)list}`);
  thm code1 = eq_mp_rule(sym_rule(code1_reduction), code1_normal);

  thm tail2_rule = ispecl_rule(TERM_LIST(
      code, `cm_ann_pc ${ann1:cm_annotation}`,
      `[${load:tvm_inst}]:(tvm_inst)list`, suffix2),
      get_cm_code_at_append_right());
  thm code2_raw = mp_rule(
      conv_rule(reduce_rewrite_conv(code_rules), tail2_rule),
      code1_normal);
  thm code2_normal =
      conv_rule(reduce_rewrite_conv(code_rules), code2_raw);
  thm code2_reduction = apply_conversion(
      reduce_rewrite_conv(code_rules),
      `cm_code_at ${code:(tvm_inst)list}
        (cm_ann_pc ${ann2:cm_annotation}) ${suffix2:(tvm_inst)list}`);
  thm code2 = eq_mp_rule(sym_rule(code2_reduction), code2_normal);

  thm tail3_rule = ispecl_rule(TERM_LIST(
      code, `cm_ann_pc ${ann2:cm_annotation}`,
      `[${push_offset:tvm_inst}]:(tvm_inst)list`, suffix3),
      get_cm_code_at_append_right());
  thm code3_raw = mp_rule(
      conv_rule(reduce_rewrite_conv(code_rules), tail3_rule),
      code2_normal);
  thm code3_normal =
      conv_rule(reduce_rewrite_conv(code_rules), code3_raw);
  thm code3_reduction = apply_conversion(
      reduce_rewrite_conv(code_rules),
      `cm_code_at ${code:(tvm_inst)list}
        (cm_ann_pc ${ann3:cm_annotation}) ${suffix3:(tvm_inst)list}`);
  thm code3 = eq_mp_rule(sym_rule(code3_reduction), code3_normal);

  thm tail4_rule = ispecl_rule(TERM_LIST(
      code, `cm_ann_pc ${ann3:cm_annotation}`,
      `[${add:tvm_inst}]:(tvm_inst)list`, suffix4),
      get_cm_code_at_append_right());
  thm code4_raw = mp_rule(
      conv_rule(reduce_rewrite_conv(code_rules), tail4_rule),
      code3_normal);
  thm code4_normal =
      conv_rule(reduce_rewrite_conv(code_rules), code4_raw);
  thm code4_reduction = apply_conversion(
      reduce_rewrite_conv(code_rules),
      `cm_code_at ${code:(tvm_inst)list}
        (cm_ann_pc ${ann4:cm_annotation}) ${suffix4:(tvm_inst)list}`);
  thm code4 = eq_mp_rule(sym_rule(code4_reduction), code4_normal);

  thm capacity = assume_rule(
      `ilength (values:(cm_value)list) < 65535i`);
  thm capacity0 = mp_rule(int_arith_rule(
      `ilength (values:(cm_value)list) < 65535i ==>
       ilength values < 65536i`), capacity);
  thm capacity1_raw = mp_rule(int_arith_rule(
      `ilength (values:(cm_value)list) < 65535i ==>
       1i + ilength values < 65536i`), capacity);
  thm capacity1_reduction = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
      `ilength
         (CMIntV (cm_state_fp (st:cm_src_state)) ::
           (values:(cm_value)list)) < 65536i`);
  thm capacity1 = eq_mp_rule(
      sym_rule(capacity1_reduction), capacity1_raw);

  thm push8_bridge = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_value_number_def(), get_tower_wrap64_def())),
      `tower_wrap64 8i ==
       cm_value_number (st:cm_src_state) (CMIntV 8i)`));
  thm sim0 = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state) (values:(cm_value)list)
        (ann:cm_annotation) (target:tvm_task)`);
  thm sim1 = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `values:(cm_value)list`, `ann:cm_annotation`,
        `target:tvm_task`, `CMIntV 8i`, `8i:int`, suffix1),
        get_cm_target_push()), code0), sim0), capacity0),
      push8_bridge);
  thm sim2 = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `values:(cm_value)list`, ann1,
        `tvm_iter 1 (target:tvm_task)`, suffix2),
        get_cm_target_load_fp()), code1), sim1),
      assume_rule(
        `tower_signed64 (cm_state_fp (st:cm_src_state))`));

  thm offset_fixed = mp_rule(spec_rule(offset,
      get_tower_wrap64_fixed()), assume_rule(
        `tower_signed64 ${offset:int}`));
  thm push_offset_bridge = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_value_number_def(), offset_fixed)),
      `tower_wrap64 ${offset:int} ==
       cm_value_number (st:cm_src_state) (CMIntV ${offset:int})`));
  thm sim3 = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `CMIntV (cm_state_fp st) :: (values:(cm_value)list)`,
        ann2, `tvm_iter 1 (tvm_iter 1 (target:tvm_task))`,
        `CMIntV ${offset:int}`, offset, suffix3),
        get_cm_target_push()), code2), sim2), capacity1),
      push_offset_bridge);

  thm fp_fixed = mp_rule(spec_rule(
      `cm_state_fp (st:cm_src_state)`, get_tower_wrap64_fixed()),
      assume_rule(
        `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  thm address_equal = assume_rule(
      `(address:int) ==
       cm_state_fp (st:cm_src_state) + ${offset:int}`);
  thm address_fixed = mp_rule(spec_rule(
      `address:int`, get_tower_wrap64_fixed()), assume_rule(
        `tower_signed64 (address:int)`));
  thm sum_fixed = conv_rule(
      rewrite_conv(THM_LIST(address_equal)), address_fixed);
  thm addition = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_value_number_def(), get_tower_add_def(), fp_fixed,
        offset_fixed, sum_fixed, address_equal)),
      `tower_add
          (cm_value_number (st:cm_src_state)
            (CMIntV (cm_state_fp st)))
          (cm_value_number st (CMIntV ${offset:int})) ==
       cm_value_number st (CMIntV (address:int))`));
  thm binary = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `CMIntV ${offset:int}`, `CMIntV (cm_state_fp st)`,
      `values:(cm_value)list`, ann3,
      `tvm_iter 1 (tvm_iter 1 (tvm_iter 1 (target:tvm_task)))`,
      `TVMAddOp:tvm_opcode`, `tower_add:int->int->int`,
      `CMIntV (address:int)`, suffix4),
      get_cm_target_binary_total());
  thm sim4 = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(binary, get_tvm_add_transition()), code3), sim3),
      addition);
  thm holds4_reduction = apply_conversion(
      reduce_rewrite_conv(code_rules),
      `cm_spill_holds (slot:int) (spill_value:cm_value)
        (cm_ann_spills ${ann4:cm_annotation})`);
  thm holds4 = eq_mp_rule(
      sym_rule(holds4_reduction), assume_rule(
        `cm_spill_holds (slot:int) (spill_value:cm_value)
          (cm_ann_spills (ann:cm_annotation))`));
  thm sim5 = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `slot:int`, `spill_value:cm_value`, `address:int`,
        `values:(cm_value)list`, ann4,
        `tvm_iter 1
          (tvm_iter 1
            (tvm_iter 1
              (tvm_iter 1 (target:tvm_task))))`,
        `rest:(tvm_inst)list`),
        get_cm_target_spill_load()), code4), sim4),
      holds4),
      assume_rule(
        `(address:int) ==
         cm_state_fp (st:cm_src_state) + ${offset:int}`)),
      assume_rule(`tower_signed64 (address:int)`)),
      assume_rule(`tower_word_valid (address:int)`));

  term final_ann =
      `cm_ann_linear
        (cm_temp_load_code (p:cm_program) (fid:int) (slot:int))
        (ann:cm_annotation)`;
  term ann5 =
      `cm_ann_linear [TVMInst TVMLoadOp 0i]
        ${ann4:cm_annotation}`;
  term target5 =
      `tvm_iter 1
        (tvm_iter 1
          (tvm_iter 1
            (tvm_iter 1
              (tvm_iter 1 (target:tvm_task)))))`;
  thm_list final_rules = THM_LIST(
      get_cm_temp_load_code_def(),
      get_cm_fp_relative_address_code_def(), get_cm_push_code_def(),
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
      cm_ann_temp_def, cm_ann_break_def, cm_ann_continue_def,
      cm_ann_cursors_def, cm_ann_spills_def, cm_ann_saved_def,
      cm_ann_calls_def, get_theorem_by_name("APPEND"),
      get_theorem_by_name("ILENGTH_DEF"));
  term pc_equality =
      `cm_ann_pc ${final_ann:cm_annotation} ==
       cm_ann_pc ${ann5:cm_annotation}`;
  thm pc_reduction = apply_conversion(
      reduce_rewrite_conv(final_rules), pc_equality);
  thm pc_normal = int_arith_rule(
      `cm_ann_pc (ann:cm_annotation) + 5i ==
       ((((cm_ann_pc ann + 1i) + 1i) + 1i) + 1i) + 1i`);
  thm same_pc = eq_mp_rule(sym_rule(pc_reduction), pc_normal);
  thm same_calls = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(final_rules),
      `cm_ann_calls ${final_ann:cm_annotation} ==
       cm_ann_calls ${ann5:cm_annotation}`));
  thm same_spills = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(final_rules),
      `cm_ann_spills ${final_ann:cm_annotation} ==
       cm_ann_spills ${ann5:cm_annotation}`));
  thm same_saved = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(final_rules),
      `cm_ann_saved ${final_ann:cm_annotation} ==
       cm_ann_saved ${ann5:cm_annotation}`));
  thm reannotated = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `(spill_value:cm_value) :: (values:(cm_value)list)`,
        ann5, final_ann, target5),
        get_cm_target_reannotate()), same_pc), same_calls),
      same_spills), same_saved), sim5);

  term desired =
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        ((spill_value:cm_value) :: (values:(cm_value)list))
        ${final_ann:cm_annotation}
        (tvm_iter 5 (target:tvm_task))`;
  vector_add(&final_rules, conjunct1_rule(get_tvm_iter_def()));
  term iter_index = `0`;
  for (size_t i = 0; i < 5; ++i) {
    thm successor = apply_conversion(
        get_conversion_by_name("NUM_SUC_CONV"),
        mk_comb(`SUC`, iter_index));
    vector_add(&final_rules, conv_rule(
        rewrite_conv(THM_LIST(successor)),
        spec_rule(iter_index, conjunct2_rule(get_tvm_iter_def()))));
    iter_index = rhs_of(successor);
  }
  thm normalized =
      conv_rule(reduce_rewrite_conv(final_rules), reannotated);
  thm reduction = apply_conversion(
      reduce_rewrite_conv(final_rules), desired);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(reduction), normalized));
  return gnode_prove(root);
}
PROOF thm cm_target_temp_load = cm_prove_target_temp_load();

PROOF static thm cm_prove_target_temp_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (slot:int) (v:cm_value) (values:(cm_value)list)
         (ann:cm_annotation) (target:tvm_task)
         (rest:(tvm_inst)list) (address:int).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (cm_temp_store_code p fid slot ++ rest) ==>
         cm_running_target_sim p fid st (v :: values) ann target ==>
         ilength values < 65534i ==>
         cm_tagged_span_valid st ==>
         (!addr.
            cm_live_address st addr ==>
            ~(address <= addr && addr < address + 8i)) ==>
         cm_range_disjoint address 8i 8i 8i ==>
         cm_call_frames_store_safe CMIntTy address
           (cm_ann_calls ann) ==>
         cm_spill_frames_store_safe p CMIntTy address
           (cm_ann_saved ann) ==>
         tower_signed64 (cm_state_fp st) ==>
         tower_signed64 (cm_temp_offset p fid slot) ==>
         address == cm_state_fp st + cm_temp_offset p fid slot ==>
         tower_signed64 address ==>
         tower_word_valid address ==>
         cm_running_target_sim p fid st values
           (cm_ann_put_spill slot v
             (cm_ann_linear
               (cm_temp_store_code p fid slot) ann))
           (tvm_iter 5 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term code = `cm_model_code (p:cm_program)`;
  term pc = `cm_ann_pc (ann:cm_annotation)`;
  term offset = `cm_temp_offset (p:cm_program) (fid:int) (slot:int)`;
  term push8 = `TVMInst TVMPushOp 8i`;
  term load = `TVMInst TVMLoadOp 0i`;
  term push_offset = `TVMInst TVMPushOp ${offset:int}`;
  term add = `TVMInst TVMAddOp 0i`;
  term store = `TVMInst TVMStoreOp 0i`;
  term suffix1 =
      `${load:tvm_inst} :: ${push_offset:tvm_inst} ::
       ${add:tvm_inst} :: ${store:tvm_inst} ::
       (rest:(tvm_inst)list)`;
  term suffix2 =
      `${push_offset:tvm_inst} :: ${add:tvm_inst} ::
       ${store:tvm_inst} :: (rest:(tvm_inst)list)`;
  term suffix3 =
      `${add:tvm_inst} :: ${store:tvm_inst} ::
       (rest:(tvm_inst)list)`;
  term suffix4 =
      `${store:tvm_inst} :: (rest:(tvm_inst)list)`;
  term ann1 =
      `cm_ann_linear (cm_push_code 8i) (ann:cm_annotation)`;
  term ann2 =
      `cm_ann_linear [TVMInst TVMLoadOp 0i]
        ${ann1:cm_annotation}`;
  term ann3 =
      `cm_ann_linear (cm_push_code ${offset:int})
        ${ann2:cm_annotation}`;
  term ann4 =
      `cm_ann_linear [TVMInst TVMAddOp 0i]
        ${ann3:cm_annotation}`;

  thm old_code = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (cm_temp_store_code p (fid:int) (slot:int) ++
          (rest:(tvm_inst)list))`);
  thm_list code_rules = THM_LIST(
      get_cm_temp_store_code_def(),
      get_cm_fp_relative_address_code_def(),
      get_cm_push_code_def(), get_theorem_by_name("APPEND"),
      get_theorem_by_name("ILENGTH_DEF"), cm_ann_linear_def,
      cm_ann_plain_def, cm_ann_pc_def, cm_ann_temp_def,
      cm_ann_break_def, cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def);
  thm code0 = conv_rule(reduce_rewrite_conv(code_rules), old_code);

  thm tail1_rule = ispecl_rule(TERM_LIST(
      code, pc, `[${push8:tvm_inst}]:(tvm_inst)list`, suffix1),
      get_cm_code_at_append_right());
  thm code1_raw = mp_rule(
      conv_rule(reduce_rewrite_conv(code_rules), tail1_rule), code0);
  thm code1_normal =
      conv_rule(reduce_rewrite_conv(code_rules), code1_raw);
  thm code1_reduction = apply_conversion(
      reduce_rewrite_conv(code_rules),
      `cm_code_at ${code:(tvm_inst)list}
        (cm_ann_pc ${ann1:cm_annotation})
        ${suffix1:(tvm_inst)list}`);
  thm code1 =
      eq_mp_rule(sym_rule(code1_reduction), code1_normal);

  thm tail2_rule = ispecl_rule(TERM_LIST(
      code, `cm_ann_pc ${ann1:cm_annotation}`,
      `[${load:tvm_inst}]:(tvm_inst)list`, suffix2),
      get_cm_code_at_append_right());
  thm code2_raw = mp_rule(
      conv_rule(reduce_rewrite_conv(code_rules), tail2_rule),
      code1_normal);
  thm code2_normal =
      conv_rule(reduce_rewrite_conv(code_rules), code2_raw);
  thm code2_reduction = apply_conversion(
      reduce_rewrite_conv(code_rules),
      `cm_code_at ${code:(tvm_inst)list}
        (cm_ann_pc ${ann2:cm_annotation})
        ${suffix2:(tvm_inst)list}`);
  thm code2 =
      eq_mp_rule(sym_rule(code2_reduction), code2_normal);

  thm tail3_rule = ispecl_rule(TERM_LIST(
      code, `cm_ann_pc ${ann2:cm_annotation}`,
      `[${push_offset:tvm_inst}]:(tvm_inst)list`, suffix3),
      get_cm_code_at_append_right());
  thm code3_raw = mp_rule(
      conv_rule(reduce_rewrite_conv(code_rules), tail3_rule),
      code2_normal);
  thm code3_normal =
      conv_rule(reduce_rewrite_conv(code_rules), code3_raw);
  thm code3_reduction = apply_conversion(
      reduce_rewrite_conv(code_rules),
      `cm_code_at ${code:(tvm_inst)list}
        (cm_ann_pc ${ann3:cm_annotation})
        ${suffix3:(tvm_inst)list}`);
  thm code3 =
      eq_mp_rule(sym_rule(code3_reduction), code3_normal);

  thm tail4_rule = ispecl_rule(TERM_LIST(
      code, `cm_ann_pc ${ann3:cm_annotation}`,
      `[${add:tvm_inst}]:(tvm_inst)list`, suffix4),
      get_cm_code_at_append_right());
  thm code4_raw = mp_rule(
      conv_rule(reduce_rewrite_conv(code_rules), tail4_rule),
      code3_normal);
  thm code4_normal =
      conv_rule(reduce_rewrite_conv(code_rules), code4_raw);
  thm code4_reduction = apply_conversion(
      reduce_rewrite_conv(code_rules),
      `cm_code_at ${code:(tvm_inst)list}
        (cm_ann_pc ${ann4:cm_annotation})
        ${suffix4:(tvm_inst)list}`);
  thm code4 =
      eq_mp_rule(sym_rule(code4_reduction), code4_normal);

  thm capacity = assume_rule(
      `ilength (values:(cm_value)list) < 65534i`);
  thm capacity0_raw = mp_rule(int_arith_rule(
      `ilength (values:(cm_value)list) < 65534i ==>
       1i + ilength values < 65536i`), capacity);
  thm capacity0 = eq_mp_rule(sym_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
      `ilength ((v:cm_value) ::
         (values:(cm_value)list)) < 65536i`)),
      capacity0_raw);
  thm capacity1_raw = mp_rule(int_arith_rule(
      `ilength (values:(cm_value)list) < 65534i ==>
       1i + 1i + ilength values < 65536i`), capacity);
  thm capacity1 = eq_mp_rule(sym_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
      `ilength
         (CMIntV (cm_state_fp (st:cm_src_state)) ::
          (v:cm_value) :: (values:(cm_value)list)) < 65536i`)),
      capacity1_raw);

  thm push8_bridge = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_value_number_def(), get_tower_wrap64_def())),
      `tower_wrap64 8i ==
       cm_value_number (st:cm_src_state) (CMIntV 8i)`));
  thm sim0 = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        ((v:cm_value) :: (values:(cm_value)list))
        (ann:cm_annotation) (target:tvm_task)`);
  thm sim1 = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `(v:cm_value) :: (values:(cm_value)list)`,
        `ann:cm_annotation`, `target:tvm_task`,
        `CMIntV 8i`, `8i:int`, suffix1),
        get_cm_target_push()), code0), sim0), capacity0),
      push8_bridge);
  thm sim2 = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `(v:cm_value) :: (values:(cm_value)list)`, ann1,
        `tvm_iter 1 (target:tvm_task)`, suffix2),
        get_cm_target_load_fp()), code1), sim1),
      assume_rule(
        `tower_signed64 (cm_state_fp (st:cm_src_state))`));

  thm offset_fixed = mp_rule(spec_rule(offset,
      get_tower_wrap64_fixed()), assume_rule(
        `tower_signed64 ${offset:int}`));
  thm push_offset_bridge = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_value_number_def(), offset_fixed)),
      `tower_wrap64 ${offset:int} ==
       cm_value_number (st:cm_src_state)
         (CMIntV ${offset:int})`));
  thm sim3 = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `CMIntV (cm_state_fp st) :: (v:cm_value) ::
          (values:(cm_value)list)`,
        ann2,
        `tvm_iter 1 (tvm_iter 1 (target:tvm_task))`,
        `CMIntV ${offset:int}`, offset, suffix3),
        get_cm_target_push()), code2), sim2), capacity1),
      push_offset_bridge);

  thm fp_fixed = mp_rule(spec_rule(
      `cm_state_fp (st:cm_src_state)`,
      get_tower_wrap64_fixed()), assume_rule(
        `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  thm address_equal = assume_rule(
      `(address:int) ==
       cm_state_fp (st:cm_src_state) + ${offset:int}`);
  thm address_fixed = mp_rule(spec_rule(
      `address:int`, get_tower_wrap64_fixed()), assume_rule(
        `tower_signed64 (address:int)`));
  thm sum_fixed = conv_rule(
      rewrite_conv(THM_LIST(address_equal)), address_fixed);
  thm addition = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_value_number_def(), get_tower_add_def(), fp_fixed,
        offset_fixed, sum_fixed, address_equal)),
      `tower_add
          (cm_value_number (st:cm_src_state)
            (CMIntV (cm_state_fp st)))
          (cm_value_number st (CMIntV ${offset:int})) ==
       cm_value_number st (CMIntV (address:int))`));
  thm binary = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `CMIntV ${offset:int}`, `CMIntV (cm_state_fp st)`,
      `(v:cm_value) :: (values:(cm_value)list)`, ann3,
      `tvm_iter 1
        (tvm_iter 1
          (tvm_iter 1 (target:tvm_task)))`,
      `TVMAddOp:tvm_opcode`, `tower_add:int->int->int`,
      `CMIntV (address:int)`, suffix4),
      get_cm_target_binary_total());
  thm sim4 = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(binary, get_tvm_add_transition()), code3),
      sim3), addition);

  thm call_safe4 = eq_mp_rule(sym_rule(apply_conversion(
      reduce_rewrite_conv(code_rules),
      `cm_call_frames_store_safe CMIntTy (address:int)
         (cm_ann_calls ${ann4:cm_annotation})`)),
      assume_rule(
        `cm_call_frames_store_safe CMIntTy (address:int)
          (cm_ann_calls (ann:cm_annotation))`));
  thm saved_safe4 = eq_mp_rule(sym_rule(apply_conversion(
      reduce_rewrite_conv(code_rules),
      `cm_spill_frames_store_safe (p:cm_program) CMIntTy
         (address:int) (cm_ann_saved ${ann4:cm_annotation})`)),
      assume_rule(
        `cm_spill_frames_store_safe (p:cm_program) CMIntTy
          (address:int) (cm_ann_saved (ann:cm_annotation))`));
  thm sim5 = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `slot:int`, `address:int`, `v:cm_value`,
          `values:(cm_value)list`, ann4,
          `tvm_iter 1
            (tvm_iter 1
              (tvm_iter 1
                (tvm_iter 1 (target:tvm_task))))`,
          `rest:(tvm_inst)list`),
          get_cm_target_spill_store()),
        code4), sim4),
        assume_rule(`cm_tagged_span_valid (st:cm_src_state)`)),
        assume_rule(
          `!addr.
             cm_live_address (st:cm_src_state) addr ==>
             ~((address:int) <= addr &&
               addr < address + 8i)`)),
        assume_rule(
          `cm_range_disjoint (address:int) 8i 8i 8i`)),
        call_safe4), saved_safe4), address_equal),
        assume_rule(`tower_signed64 (address:int)`)),
        assume_rule(`tower_word_valid (address:int)`));

  term final_ann =
      `cm_ann_put_spill (slot:int) (v:cm_value)
        (cm_ann_linear
          (cm_temp_store_code (p:cm_program) (fid:int) slot)
          (ann:cm_annotation))`;
  term ann5 =
      `cm_ann_put_spill (slot:int) (v:cm_value)
        (cm_ann_linear [TVMInst TVMStoreOp 0i]
          ${ann4:cm_annotation})`;
  term target5 =
      `tvm_iter 1
        (tvm_iter 1
          (tvm_iter 1
            (tvm_iter 1
              (tvm_iter 1 (target:tvm_task)))))`;
  thm_list final_rules = THM_LIST(
      get_cm_temp_store_code_def(),
      get_cm_fp_relative_address_code_def(),
      get_cm_push_code_def(), cm_ann_put_spill_def,
      cm_ann_spills_set_def, cm_spill_put_def,
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
      cm_ann_temp_def, cm_ann_break_def, cm_ann_continue_def,
      cm_ann_cursors_def, cm_ann_spills_def, cm_ann_saved_def,
      cm_ann_calls_def, get_theorem_by_name("APPEND"),
      get_theorem_by_name("ILENGTH_DEF"));
  thm pc_reduction = apply_conversion(
      reduce_rewrite_conv(final_rules),
      `cm_ann_pc ${final_ann:cm_annotation} ==
       cm_ann_pc ${ann5:cm_annotation}`);
  thm pc_normal = int_arith_rule(
      `cm_ann_pc (ann:cm_annotation) + 5i ==
       ((((cm_ann_pc ann + 1i) + 1i) + 1i) + 1i) + 1i`);
  thm same_pc =
      eq_mp_rule(sym_rule(pc_reduction), pc_normal);
  thm same_calls = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(final_rules),
      `cm_ann_calls ${final_ann:cm_annotation} ==
       cm_ann_calls ${ann5:cm_annotation}`));
  thm same_spills = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(final_rules),
      `cm_ann_spills ${final_ann:cm_annotation} ==
       cm_ann_spills ${ann5:cm_annotation}`));
  thm same_saved = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(final_rules),
      `cm_ann_saved ${final_ann:cm_annotation} ==
       cm_ann_saved ${ann5:cm_annotation}`));
  thm reannotated = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `values:(cm_value)list`, ann5, final_ann, target5),
        get_cm_target_reannotate()), same_pc), same_calls),
      same_spills), same_saved), sim5);

  term desired =
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state) (values:(cm_value)list)
        ${final_ann:cm_annotation}
        (tvm_iter 5 (target:tvm_task))`;
  vector_add(&final_rules, conjunct1_rule(get_tvm_iter_def()));
  term iter_index = `0`;
  for (size_t i = 0; i < 5; ++i) {
    thm successor = apply_conversion(
        get_conversion_by_name("NUM_SUC_CONV"),
        mk_comb(`SUC`, iter_index));
    vector_add(&final_rules, conv_rule(
        rewrite_conv(THM_LIST(successor)),
        spec_rule(iter_index, conjunct2_rule(get_tvm_iter_def()))));
    iter_index = rhs_of(successor);
  }
  thm normalized =
      conv_rule(reduce_rewrite_conv(final_rules), reannotated);
  thm reduction = apply_conversion(
      reduce_rewrite_conv(final_rules), desired);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(reduction), normalized));
  return gnode_prove(root);
}
PROOF thm cm_target_temp_store =
    cm_prove_target_temp_store();

PROOF thm get_cm_target_temp_load(void) {
  return cm_target_temp_load;
}
PROOF thm get_cm_target_temp_store(void) {
  return cm_target_temp_store;
}


PROOF static int cmc_preservation_target_spill_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_spill_axioms_before,
      "cmc_preservation_target_spill introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_spill_checks =
    cmc_preservation_target_spill_final_checks();
