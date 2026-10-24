#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_code.h"
#include "cmc_preservation_target_address.h"

#require "cmc_preservation_code.c"
#require "cmc_preservation_target_machine.c"

PROOF static size_t _cmc_preservation_target_address_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_target_fp_relative_address(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (offset:int) (address:int) (address_value:cm_value)
         (values:(cm_value)list) (ann:cm_annotation)
         (target:tvm_task) (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (cm_fp_relative_address_code offset ++ rest) ==>
         cm_running_target_sim p fid st values ann target ==>
         ilength values < 65535i ==>
         tower_signed64 (cm_state_fp st) ==>
         tower_signed64 offset ==>
         address == cm_state_fp st + offset ==>
         tower_signed64 address ==>
         tower_wrap64 address == cm_value_number st address_value ==>
         cm_running_target_sim p fid st (address_value :: values)
           (cm_ann_linear (cm_fp_relative_address_code offset) ann)
           (tvm_iter 4 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term code = `cm_model_code (p:cm_program)`;
  term pc = `cm_ann_pc (ann:cm_annotation)`;
  term push8 = `TVMInst TVMPushOp 8i`;
  term load = `TVMInst TVMLoadOp 0i`;
  term push_offset = `TVMInst TVMPushOp (offset:int)`;
  term add = `TVMInst TVMAddOp 0i`;
  term suffix1 =
      `${load:tvm_inst} :: ${push_offset:tvm_inst} ::
       ${add:tvm_inst} :: (rest:(tvm_inst)list)`;
  term suffix2 =
      `${push_offset:tvm_inst} :: ${add:tvm_inst} ::
       (rest:(tvm_inst)list)`;
  term suffix3 = `${add:tvm_inst} :: (rest:(tvm_inst)list)`;
  term ann1 =
      `cm_ann_linear (cm_push_code 8i) (ann:cm_annotation)`;
  term ann2 =
      `cm_ann_linear [TVMInst TVMLoadOp 0i] ${ann1:cm_annotation}`;
  term ann3 =
      `cm_ann_linear (cm_push_code (offset:int))
        ${ann2:cm_annotation}`;

  thm old_code = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (cm_fp_relative_address_code (offset:int) ++
          (rest:(tvm_inst)list))`);
  thm_list code_rules = THM_LIST(
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

  thm offset_fixed = mp_rule(spec_rule(`offset:int`,
      get_tower_wrap64_fixed()), assume_rule(
        `tower_signed64 (offset:int)`));
  thm push_offset_bridge = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_value_number_def(), offset_fixed)),
      `tower_wrap64 (offset:int) ==
       cm_value_number (st:cm_src_state) (CMIntV offset)`));
  thm sim3 = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `CMIntV (cm_state_fp st) :: (values:(cm_value)list)`,
        ann2, `tvm_iter 1 (tvm_iter 1 (target:tvm_task))`,
        `CMIntV (offset:int)`, `offset:int`, suffix3),
        get_cm_target_push()), code2), sim2), capacity1),
      push_offset_bridge);

  thm fp_fixed = mp_rule(spec_rule(
      `cm_state_fp (st:cm_src_state)`, get_tower_wrap64_fixed()),
      assume_rule(
        `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  thm address_equal = assume_rule(
      `(address:int) ==
       cm_state_fp (st:cm_src_state) + (offset:int)`);
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
          (cm_value_number st (CMIntV (offset:int))) ==
       cm_value_number st (CMIntV (address:int))`));
  thm binary = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `CMIntV (offset:int)`, `CMIntV (cm_state_fp st)`,
      `values:(cm_value)list`, ann3,
      `tvm_iter 1 (tvm_iter 1 (tvm_iter 1 (target:tvm_task)))`,
      `TVMAddOp:tvm_opcode`, `tower_add:int->int->int`,
      `CMIntV (address:int)`, `rest:(tvm_inst)list`),
      get_cm_target_binary_total());
  thm sim4 = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(binary, get_tvm_add_transition()), code3), sim3),
      addition);

  term revalue_equality =
      `cm_value_number (st:cm_src_state) (CMIntV (address:int)) ==
       cm_value_number st (address_value:cm_value)`;
  thm revalue_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_value_number_def())),
      revalue_equality);
  thm number_equal = eq_mp_rule(sym_rule(revalue_view), assume_rule(
      `tower_wrap64 (address:int) ==
       cm_value_number (st:cm_src_state) (address_value:cm_value)`));
  thm revalued = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `CMIntV (address:int)`, `address_value:cm_value`,
      `values:(cm_value)list`,
      `cm_ann_linear [TVMInst TVMAddOp 0i] ${ann3:cm_annotation}`,
      `tvm_iter 1
        (tvm_iter 1
          (tvm_iter 1
            (tvm_iter 1 (target:tvm_task))))`),
      get_cm_target_revalue()), number_equal), sim4);

  term final_ann =
      `cm_ann_linear
        (cm_fp_relative_address_code (offset:int))
        (ann:cm_annotation)`;
  term ann4 =
      `cm_ann_linear [TVMInst TVMAddOp 0i]
        ${ann3:cm_annotation}`;
  term target4 =
      `tvm_iter 1
        (tvm_iter 1
          (tvm_iter 1
            (tvm_iter 1 (target:tvm_task))))`;
  thm_list final_rules = THM_LIST(
      get_cm_fp_relative_address_code_def(), get_cm_push_code_def(),
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
      cm_ann_temp_def, cm_ann_break_def, cm_ann_continue_def,
      cm_ann_cursors_def, cm_ann_spills_def, cm_ann_saved_def,
      cm_ann_calls_def, get_theorem_by_name("APPEND"),
      get_theorem_by_name("ILENGTH_DEF"));
  thm pc_reduction = apply_conversion(
      reduce_rewrite_conv(final_rules),
      `cm_ann_pc ${final_ann:cm_annotation} ==
       cm_ann_pc ${ann4:cm_annotation}`);
  thm pc_normal = int_arith_rule(
      `cm_ann_pc (ann:cm_annotation) + 4i ==
       (((cm_ann_pc ann + 1i) + 1i) + 1i) + 1i`);
  thm same_pc = eq_mp_rule(sym_rule(pc_reduction), pc_normal);
  thm same_calls = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(final_rules),
      `cm_ann_calls ${final_ann:cm_annotation} ==
       cm_ann_calls ${ann4:cm_annotation}`));
  thm same_spills = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(final_rules),
      `cm_ann_spills ${final_ann:cm_annotation} ==
       cm_ann_spills ${ann4:cm_annotation}`));
  thm same_saved = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(final_rules),
      `cm_ann_saved ${final_ann:cm_annotation} ==
       cm_ann_saved ${ann4:cm_annotation}`));
  thm reannotated = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `(address_value:cm_value) :: (values:(cm_value)list)`,
        ann4, final_ann, target4),
        get_cm_target_reannotate()), same_pc), same_calls),
      same_spills), same_saved), revalued);

  term desired =
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        ((address_value:cm_value) :: (values:(cm_value)list))
        ${final_ann:cm_annotation}
        (tvm_iter 4 (target:tvm_task))`;
  vector_add(&final_rules, conjunct1_rule(get_tvm_iter_def()));
  term iter_index = `0`;
  for (size_t index = 0; index < 4; ++index) {
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

PROOF thm cm_target_fp_relative_address =
    cm_prove_target_fp_relative_address();

PROOF static thm cm_prove_target_binding_address(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (scope:int) (slot:int) (address:int)
         (address_value:cm_value) (values:(cm_value)list)
         (ann:cm_annotation) (target:tvm_task)
         (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (cm_binding_address_code p fid scope slot ++ rest) ==>
         cm_running_target_sim p fid st values ann target ==>
         ilength values < 65535i ==>
         (scope == 0i ||
          (tower_signed64 (cm_state_fp st) &&
           tower_signed64
             (if scope == 1i then cm_local_offset p fid slot
              else cm_param_offset p fid slot))) ==>
         address ==
           (if scope == 0i then cm_global_address p slot
            else cm_state_fp st +
              (if scope == 1i then cm_local_offset p fid slot
               else cm_param_offset p fid slot)) ==>
         tower_signed64 address ==>
         tower_wrap64 address ==
           cm_value_number st address_value ==>
         cm_running_target_sim p fid st (address_value :: values)
           (cm_ann_linear
             (cm_binding_address_code p fid scope slot) ann)
           (tvm_iter
             (cm_code_steps
               (cm_binding_address_code p fid scope slot))
             target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term binding_offset =
      `(if (scope:int) == 1i
        then cm_local_offset (p:cm_program) (fid:int) (slot:int)
        else cm_param_offset p fid slot)`;
  thm old_code = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (cm_binding_address_code p (fid:int) (scope:int) (slot:int) ++
          (rest:(tvm_inst)list))`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state) (values:(cm_value)list)
        (ann:cm_annotation) (target:tvm_task)`);
  thm capacity = assume_rule(
      `ilength (values:(cm_value)list) < 65535i`);
  thm relative_ready = assume_rule(
      `(scope:int) == 0i ||
       (tower_signed64 (cm_state_fp (st:cm_src_state)) &&
        tower_signed64 ${binding_offset:int})`);
  thm capacity_push = mp_rule(int_arith_rule(
      `ilength (values:(cm_value)list) < 65535i ==>
       ilength values < 65536i`), capacity);
  thm address_equal = assume_rule(
      `(address:int) ==
       (if (scope:int) == 0i
        then cm_global_address (p:cm_program) (slot:int)
        else cm_state_fp (st:cm_src_state) + ${binding_offset:int})`);
  thm number_equal = assume_rule(
      `tower_wrap64 (address:int) ==
       cm_value_number (st:cm_src_state) (address_value:cm_value)`);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(scope:int) == 0i`, "Hglobal");
  {
    thm global_case = assume_rule(`(scope:int) == 0i`);
    thm code_at = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_binding_address_code_def(), get_cm_push_code_def(),
        global_case, get_theorem_by_name("APPEND"))), old_code);
    thm global_address = conv_rule(
        reduce_rewrite_conv(THM_LIST(global_case)), address_equal);
    thm global_number = conv_rule(
        rewrite_conv(THM_LIST(global_address)), number_equal);
    thm result = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `values:(cm_value)list`, `ann:cm_annotation`,
        `target:tvm_task`, `address_value:cm_value`,
        `cm_global_address (p:cm_program) (slot:int)`,
        `rest:(tvm_inst)list`), get_cm_target_push());
    result = match_mp_rule(match_mp_rule(match_mp_rule(
        match_mp_rule(result, code_at), running), capacity_push),
        global_number);
    thm num_of_int_one = spec_rule(
        `1:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM"));
    thm_list rules = THM_LIST(
        get_cm_binding_address_code_def(), get_cm_push_code_def(),
        global_case, cm_code_steps_def, cm_ann_linear_def,
        cm_ann_plain_def, get_theorem_by_name("APPEND"),
        get_theorem_by_name("ILENGTH_DEF"), num_of_int_one);
    conv normalize = then_conv(
        reduce_rewrite_conv(rules),
        rewrite_conv(THM_LIST(num_of_int_one)));
    thm normalized = conv_rule(normalize, result);
    thm target_view =
        apply_conversion(normalize, goal_ccl(cases[0]->g));
    ACCEPT_TAC(cases[0],
        eq_mp_rule(sym_rule(target_view), normalized));
  }
  {
    thm local_case = assume_rule(`~((scope:int) == 0i)`);
    thm code_at = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_binding_address_code_def(), local_case)), old_code);
    thm local_address = conv_rule(
        reduce_rewrite_conv(THM_LIST(local_case)), address_equal);
    thm result = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        binding_offset, `address:int`, `address_value:cm_value`,
        `values:(cm_value)list`, `ann:cm_annotation`,
        `target:tvm_task`, `rest:(tvm_inst)list`),
        cm_target_fp_relative_address);
    thm relative_pair = mp_rule(mp_rule(
        taut_rule(imp_chain(TERM_LIST(
          concl(relative_ready), concl(local_case)),
          `tower_signed64 (cm_state_fp (st:cm_src_state)) &&
           tower_signed64 ${binding_offset:int}`)),
        relative_ready), local_case);
    result = match_mp_rule(match_mp_rule(match_mp_rule(
        match_mp_rule(match_mp_rule(match_mp_rule(match_mp_rule(
          match_mp_rule(result, code_at), running), capacity),
          conjunct1_rule(relative_pair)),
          conjunct2_rule(relative_pair)),
          local_address),
          assume_rule(`tower_signed64 (address:int)`)),
          number_equal);
    thm num_of_int_four = spec_rule(
        `4:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM"));
    thm_list rules = THM_LIST(
        get_cm_binding_address_code_def(), local_case,
        cm_code_steps_def,
        get_cm_fp_relative_address_code_def(),
        get_theorem_by_name("ILENGTH_DEF"), num_of_int_four);
    conv normalize = then_conv(
        reduce_rewrite_conv(rules),
        rewrite_conv(THM_LIST(num_of_int_four)));
    thm normalized = conv_rule(normalize, result);
    thm target_view =
        apply_conversion(normalize, goal_ccl(cases[1]->g));
    ACCEPT_TAC(cases[1],
        eq_mp_rule(sym_rule(target_view), normalized));
  }
  return gnode_prove(root);
}

PROOF thm cm_target_binding_address =
    cm_prove_target_binding_address();


PROOF thm get_cm_target_fp_relative_address(void) {
  return cm_target_fp_relative_address;
}
PROOF thm get_cm_target_binding_address(void) {
  return cm_target_binding_address;
}


PROOF static int cmc_preservation_target_address_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_address_axioms_before,
      "cmc_preservation_target_address introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_address_checks =
    cmc_preservation_target_address_final_checks();
