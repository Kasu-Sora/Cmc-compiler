#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_convert.h"

#require "cmc_preservation_target_machine.c"

PROOF static size_t _cmc_preservation_target_convert_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_char_normalize_number(void) {
  gnode root = gnode_new_with_ccl(
      `!z. tower_signed64 (z:int) ==>
        tower_mod
          (tower_add (tower_mod z 256i) 256i) 256i ==
        tower_u8 z`);
  gnode with_z = GEN_TAC(root, "z");
  gnode leaf = DISCH_TAC(with_z, "Hzsigned");
  gnode_list zero_cases = BOOL_CASES_TAC(leaf, `(z:int) == 0i`, "Hzero");
  {
    CONV_WITH_ASMP_TAC(zero_cases[0], reduce_rewrite_conv, THM_LIST(
        get_tower_mod_def(), get_tower_add_def(),
        get_tower_trem_def(), get_tower_tquot_def(),
        get_tower_wrap64_def(), get_tower_u8_def()));
  }
  {
    gnode_list sign_cases =
        BOOL_CASES_TAC(zero_cases[1], `(z:int) < 0i`, "Hnegative");
    for (size_t i = 0; i < vector_size(sign_cases); ++i) {
      bool negative = i == 0;
      gnode branch = sign_cases[i];
      thm nonzero = assume_rule(`~((z:int) == 0i)`);
      thm sign = assume_rule(negative
          ? `(z:int) < 0i`
          : `~((z:int) < 0i)`);
      term magnitude = negative ? `--(z:int)` : `z:int`;
      thm z_abs_sign = negative
          ? mp_rule(int_arith_rule(
              `(z:int) < 0i ==> ~(0i <= z)`), sign)
          : mp_rule(int_arith_rule(
              `~((z:int) < 0i) ==> 0i <= z`), sign);
      thm abs_z = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_theorem_by_name("INT_ABS"), z_abs_sign)),
          `abs (z:int) == ${magnitude:int}`));
      thm magnitude_nonnegative = negative
          ? mp_rule(int_arith_rule(`(z:int) < 0i ==> 0i <= --z`), sign)
          : z_abs_sign;
      thm division = mp_rule(specl_rule(TERM_LIST(
          magnitude, `256i`), get_theorem_by_name("INT_DIVISION")),
          eqf_elim_rule(apply_conversion(
            reduce_rewrite_conv(THM_LIST()), `(256i:int) == 0i`)));
      thm remainder_lower = conjunct1_rule(conjunct2_rule(division));
      thm remainder_upper = conv_rule(reduce_rewrite_conv(THM_LIST()),
          conjunct2_rule(conjunct2_rule(division)));
      term remainder = `${magnitude:int} % 256i`;
      thm remainder_raw_signed = mp_rule(mp_rule(int_arith_rule(
          `0i <= (${remainder:int}) ==>
           (${remainder:int}) < 256i ==>
           --9223372036854775808i <= (${remainder:int}) &&
           (${remainder:int}) <= 9223372036854775807i`),
          remainder_lower), remainder_upper);
      thm remainder_signed = eq_mp_rule(sym_rule(apply_conversion(
          rewrite_conv(THM_LIST(get_tower_signed64_def())),
          `tower_signed64 (${remainder:int})`)), remainder_raw_signed);
      thm remainder_wrap = mp_rule(
          spec_rule(remainder, get_tower_wrap64_fixed()), remainder_signed);
      thm remainder_fixed = mp_rule(
          spec_rule(remainder, get_tower_u8_fixed()),
          eq_mp_rule(sym_rule(apply_conversion(
            rewrite_conv(THM_LIST(get_tower_byte_value_def())),
            `tower_byte_value (${remainder:int})`)),
            conj_rule(remainder_lower, remainder_upper)));
      term quotient = negative
          ? `--((${magnitude:int}) / 256i)`
          : `(z:int) / 256i`;
      thm qeq = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_tower_tquot_def(), nonzero, sign, abs_z)),
          `tower_tquot (z:int) 256i == ${quotient:int}`));
      thm divsimp = specl_rule(TERM_LIST(
          magnitude, `256i`),
          get_theorem_by_name("INT_DIVISION_SIMP"));
      thm trem_raw = negative
          ? mp_rule(int_arith_rule(
              `(${magnitude:int}) / 256i * 256i +
                 (${remainder:int}) == (${magnitude:int}) ==>
               (z:int) - --((${magnitude:int}) / 256i) * 256i ==
                 --(${remainder:int})`), divsimp)
          : mp_rule(int_arith_rule(
              `(z:int) / 256i * 256i + (${remainder:int}) == z ==>
               z - (z / 256i) * 256i == (${remainder:int})`),
              divsimp);
      term first_value = negative ? `--(${remainder:int})` : remainder;
      thm trem = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_tower_trem_def(), qeq, trem_raw)),
          `tower_trem (z:int) 256i == ${first_value:int}`));
      thm first_signed = negative
          ? eq_mp_rule(sym_rule(apply_conversion(
              rewrite_conv(THM_LIST(get_tower_signed64_def())),
              `tower_signed64 (--(${remainder:int}))`)),
              mp_rule(mp_rule(int_arith_rule(
                `0i <= (${remainder:int}) ==>
                 (${remainder:int}) < 256i ==>
                 --9223372036854775808i <= --(${remainder:int}) &&
                 --(${remainder:int}) <= 9223372036854775807i`),
                remainder_lower), remainder_upper))
          : remainder_signed;
      thm first_wrap = mp_rule(
          spec_rule(first_value, get_tower_wrap64_fixed()), first_signed);
      thm first_mod = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_tower_mod_def(), trem, first_wrap)),
          `tower_mod (z:int) 256i == ${first_value:int}`));
      term sum = `${first_value:int} + 256i`;
      thm sum_signed = eq_mp_rule(sym_rule(apply_conversion(
          rewrite_conv(THM_LIST(get_tower_signed64_def())),
          `tower_signed64 (${sum:int})`)),
          mp_rule(mp_rule(int_arith_rule(
            `0i <= (${remainder:int}) ==>
             (${remainder:int}) < 256i ==>
             --9223372036854775808i <= (${sum:int}) &&
             (${sum:int}) <= 9223372036854775807i`),
            remainder_lower), remainder_upper));
      thm sum_wrap = mp_rule(
          spec_rule(sum, get_tower_wrap64_fixed()), sum_signed);
      thm sum_add = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_tower_add_def(), sum_wrap)),
          `tower_add (${first_value:int}) 256i == ${sum:int}`));
      thm sum_positive = mp_rule(mp_rule(int_arith_rule(
          `0i <= (${remainder:int}) ==>
           (${remainder:int}) < 256i ==>
           0i < (${sum:int})`), remainder_lower), remainder_upper);
      thm sum_nonzero = mp_rule(
          int_arith_rule(`0i < (${sum:int}) ==> ~(${sum:int} == 0i)`),
          sum_positive);
      thm sum_nonnegative = mp_rule(
          int_arith_rule(`0i < (${sum:int}) ==> 0i <= (${sum:int})`),
          sum_positive);
      thm sum_not_negative = mp_rule(
          int_arith_rule(`0i < (${sum:int}) ==> ~((${sum:int}) < 0i)`),
          sum_positive);
      thm abs_sum = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_theorem_by_name("INT_ABS"), sum_nonnegative)),
          `abs (${sum:int}) == ${sum:int}`));
      thm sum_qeq = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_tower_tquot_def(), sum_nonzero, sum_not_negative, abs_sum)),
          `tower_tquot (${sum:int}) 256i ==
           (${sum:int}) / 256i`));
      thm sum_divsimp = specl_rule(TERM_LIST(
          sum, `256i`), get_theorem_by_name("INT_DIVISION_SIMP"));
      thm sum_trem_raw = mp_rule(int_arith_rule(
          `(${sum:int}) / 256i * 256i + (${sum:int}) % 256i ==
             (${sum:int}) ==>
           (${sum:int}) - ((${sum:int}) / 256i) * 256i ==
             (${sum:int}) % 256i`), sum_divsimp);
      thm sum_trem = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_tower_trem_def(), sum_qeq, sum_trem_raw)),
          `tower_trem (${sum:int}) 256i ==
           (${sum:int}) % 256i`));
      thm sum_rem = specl_rule(TERM_LIST(
          `1i`, `256i`, first_value),
          conjunct1_rule(get_theorem_by_name("INT_REM_MUL_ADD")));
      thm sum_rem_simple = conv_rule(
          reduce_rewrite_conv(THM_LIST()), sum_rem);
      thm sum_comm = specl_rule(TERM_LIST(first_value, `256i`),
          get_theorem_by_name("INT_ADD_SYM"));
      thm sum_mod_comm = mk_binop_rule(
          `(%):int->int->int`, sum_comm, refl_rule(`256i`));
      thm neg_magnitude = negative
          ? spec_rule(`z:int`, get_theorem_by_name("INT_NEG_NEG"))
          : refl_rule(`--(${magnitude:int})`);
      thm neg_magnitude_mod = mk_binop_rule(
          `(%):int->int->int`, neg_magnitude, refl_rule(`256i`));
      thm final_rem = negative
          ? trans_rule(sum_mod_comm,
              trans_rule(sum_rem_simple,
                trans_rule(
                  specl_rule(TERM_LIST(magnitude, `256i`),
                    get_theorem_by_name("INT_NEG_REM")),
                  neg_magnitude_mod)))
          : trans_rule(sum_mod_comm,
              trans_rule(sum_rem_simple,
                specl_rule(TERM_LIST(magnitude, `256i`),
                  get_theorem_by_name("INT_REM_REM"))));
      thm final_byte = conv_rule(rewrite_conv(THM_LIST(
          get_tower_byte_value_def(), get_tower_u8_def())),
          spec_rule(`z:int`, get_tower_u8_range()));
      thm final_raw_signed = mp_rule(int_arith_rule(
          `0i <= (z:int) % 256i && z % 256i < 256i ==>
           --9223372036854775808i <= z % 256i &&
           z % 256i <= 9223372036854775807i`), final_byte);
      thm final_signed = eq_mp_rule(sym_rule(apply_conversion(
          rewrite_conv(THM_LIST(get_tower_signed64_def())),
          `tower_signed64 ((z:int) % 256i)`)), final_raw_signed);
      thm final_wrap = mp_rule(spec_rule(`(z:int) % 256i`,
          get_tower_wrap64_fixed()), final_signed);
      thm second_mod = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_tower_mod_def(), sum_trem, final_rem, final_wrap)),
          `tower_mod (${sum:int}) 256i == (z:int) % 256i`));
      thm result = apply_conversion(reduce_rewrite_conv(THM_LIST(
          first_mod, sum_add, second_mod, get_tower_u8_def())),
          `tower_mod
            (tower_add (tower_mod (z:int) 256i) 256i) 256i ==
          tower_u8 z`);
      ACCEPT_TAC(branch, eqt_elim_rule(result));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_char_normalize_number =
    cm_prove_char_normalize_number();

PROOF static thm cm_target_convert_code_tail(
    const thm current_code, const term code,
    const term current_ann, const term inst,
    const term suffix, const term next_ann,
    const thm_list rules) {
  thm tail_rule = ispecl_rule(TERM_LIST(
      code, `cm_ann_pc ${current_ann:cm_annotation}`,
      `[${inst:tvm_inst}]:(tvm_inst)list`, suffix),
      get_cm_code_at_append_right());
  thm current_normal =
      conv_rule(reduce_rewrite_conv(rules), current_code);
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

PROOF static thm cm_target_convert_capacity(
    const term head, const thm capacity) {
  thm raw = mp_rule(int_arith_rule(
      `ilength (values:(cm_value)list) < 65535i ==>
       1i + ilength values < 65536i`), capacity);
  thm view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
      `ilength
        (${head:cm_value} :: (values:(cm_value)list)) < 65536i`);
  return eq_mp_rule(sym_rule(view), raw);
}

PROOF static thm cm_prove_target_char_normalize(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ty:cm_type) (v:cm_value) (values:(cm_value)list)
         (ann:cm_annotation) (target:tvm_task)
         (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (cm_char_normalize_code ty ++ rest) ==>
         cm_running_target_sim p fid st (v :: values) ann target ==>
         ilength values < 65535i ==>
         tower_signed64 (cm_value_number st v) ==>
         cm_running_target_sim p fid st
           (cm_convert_value st ty v :: values)
           (cm_ann_linear (cm_char_normalize_code ty) ann)
           (tvm_iter
             (cm_code_steps (cm_char_normalize_code ty))
             target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list type_cases = BOOL_CASES_TAC(
      leaf, `(ty:cm_type) == CMCharTy`, "Hchar");

  {
    gnode branch = type_cases[0];
    thm is_char = assume_rule(`(ty:cm_type) == CMCharTy`);
    term code = `cm_model_code (p:cm_program)`;
    term push = `TVMInst TVMPushOp 256i`;
    term mod = `TVMInst TVMModOp 0i`;
    term add = `TVMInst TVMAddOp 0i`;
    term suffix1 =
        `${mod:tvm_inst} :: ${push:tvm_inst} ::
         ${add:tvm_inst} :: ${push:tvm_inst} ::
         ${mod:tvm_inst} :: (rest:(tvm_inst)list)`;
    term suffix2 =
        `${push:tvm_inst} :: ${add:tvm_inst} ::
         ${push:tvm_inst} :: ${mod:tvm_inst} ::
         (rest:(tvm_inst)list)`;
    term suffix3 =
        `${add:tvm_inst} :: ${push:tvm_inst} ::
         ${mod:tvm_inst} :: (rest:(tvm_inst)list)`;
    term suffix4 =
        `${push:tvm_inst} :: ${mod:tvm_inst} ::
         (rest:(tvm_inst)list)`;
    term suffix5 =
        `${mod:tvm_inst} :: (rest:(tvm_inst)list)`;
    term ann1 =
        `cm_ann_linear (cm_push_code 256i) (ann:cm_annotation)`;
    term ann2 =
        `cm_ann_linear [${mod:tvm_inst}] ${ann1:cm_annotation}`;
    term ann3 =
        `cm_ann_linear (cm_push_code 256i) ${ann2:cm_annotation}`;
    term ann4 =
        `cm_ann_linear [${add:tvm_inst}] ${ann3:cm_annotation}`;
    term ann5 =
        `cm_ann_linear (cm_push_code 256i) ${ann4:cm_annotation}`;
    term ann6 =
        `cm_ann_linear [${mod:tvm_inst}] ${ann5:cm_annotation}`;
    term number =
        `cm_value_number (st:cm_src_state) (v:cm_value)`;
    term first_number =
        `tower_mod ${number:int} 256i`;
    term first_value =
        `CMIntV (${first_number:int})`;
    term sum_number =
        `tower_add (${first_number:int}) 256i`;
    term sum_value =
        `CMIntV (${sum_number:int})`;
    term final_number =
        `tower_mod (${sum_number:int}) 256i`;
    term final_value =
        `CMIntV (${final_number:int})`;

    thm_list code_rules = THM_LIST(
        get_cm_char_normalize_code_def(), is_char,
        get_cm_push_code_def(), get_theorem_by_name("APPEND"),
        get_theorem_by_name("ILENGTH_DEF"),
        cm_ann_linear_def, cm_ann_plain_def,
        cm_ann_pc_def, cm_ann_temp_def,
        cm_ann_break_def, cm_ann_continue_def,
        cm_ann_cursors_def, cm_ann_spills_def,
        cm_ann_saved_def, cm_ann_calls_def);
    thm old_code = assume_rule(
        `cm_code_at (cm_model_code (p:cm_program))
          (cm_ann_pc (ann:cm_annotation))
          (cm_char_normalize_code (ty:cm_type) ++
            (rest:(tvm_inst)list))`);
    thm code0 =
        conv_rule(reduce_rewrite_conv(code_rules), old_code);
    thm code1 = cm_target_convert_code_tail(
        code0, code, `ann:cm_annotation`, push,
        suffix1, ann1, code_rules);
    thm code2 = cm_target_convert_code_tail(
        code1, code, ann1, mod, suffix2, ann2, code_rules);
    thm code3 = cm_target_convert_code_tail(
        code2, code, ann2, push, suffix3, ann3, code_rules);
    thm code4 = cm_target_convert_code_tail(
        code3, code, ann3, add, suffix4, ann4, code_rules);
    thm code5 = cm_target_convert_code_tail(
        code4, code, ann4, push, suffix5, ann5, code_rules);

    thm capacity = assume_rule(
        `ilength (values:(cm_value)list) < 65535i`);
    thm capacity_v =
        cm_target_convert_capacity(`v:cm_value`, capacity);
    thm capacity_first =
        cm_target_convert_capacity(first_value, capacity);
    thm capacity_sum =
        cm_target_convert_capacity(sum_value, capacity);

    thm signed_256 = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(get_tower_signed64_def())),
        `tower_signed64 256i`));
    thm fixed_256 = mp_rule(
        spec_rule(`256i`, get_tower_wrap64_fixed()), signed_256);
    thm push_bridge = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_value_number_def(), fixed_256)),
        `tower_wrap64 256i ==
         cm_value_number (st:cm_src_state) (CMIntV 256i)`));

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
          `CMIntV 256i`, `256i:int`, suffix1),
          get_cm_target_push()), code0), sim0), capacity_v),
        push_bridge);

    thm mod1_bridge = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_value_number_def(), fixed_256,
          get_tower_mod_def(), get_tower_wrap64_idempotent())),
        `tower_mod
           (cm_value_number (st:cm_src_state) (v:cm_value))
           (cm_value_number st (CMIntV 256i)) ==
         cm_value_number st ${first_value:cm_value}`));
    thm mod1 = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `CMIntV 256i`, `v:cm_value`,
        `values:(cm_value)list`, ann1,
        `tvm_iter 1 (target:tvm_task)`,
        `TVMModOp:tvm_opcode`, `tower_mod:int->int->int`,
        first_value, suffix2),
        get_cm_target_binary_nonzero());
    thm sim2 = match_mp_rule(match_mp_rule(match_mp_rule(
        match_mp_rule(match_mp_rule(mod1,
          get_tvm_mod_transition()), code1), sim1),
        eqf_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_value_number_def(), fixed_256)),
          `cm_value_number (st:cm_src_state) (CMIntV 256i) ==
           0i`))), mod1_bridge);

    thm sim3 = match_mp_rule(match_mp_rule(match_mp_rule(
        match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `${first_value:cm_value} ::
            (values:(cm_value)list)`,
          ann2, `tvm_iter 1 (tvm_iter 1 (target:tvm_task))`,
          `CMIntV 256i`, `256i:int`, suffix3),
          get_cm_target_push()), code2), sim2), capacity_first),
        push_bridge);

    thm add_bridge = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_value_number_def(), fixed_256,
          get_tower_add_def(), get_tower_mod_def(),
          get_tower_wrap64_idempotent())),
        `tower_add
           (cm_value_number (st:cm_src_state)
             ${first_value:cm_value})
           (cm_value_number st (CMIntV 256i)) ==
         cm_value_number st ${sum_value:cm_value}`));
    thm addition = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `CMIntV 256i`, first_value,
        `values:(cm_value)list`, ann3,
        `tvm_iter 1
          (tvm_iter 1 (tvm_iter 1 (target:tvm_task)))`,
        `TVMAddOp:tvm_opcode`, `tower_add:int->int->int`,
        sum_value, suffix4),
        get_cm_target_binary_total());
    thm sim4 = match_mp_rule(match_mp_rule(match_mp_rule(
        match_mp_rule(addition, get_tvm_add_transition()), code3),
        sim3), add_bridge);

    thm sim5 = match_mp_rule(match_mp_rule(match_mp_rule(
        match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `${sum_value:cm_value} ::
            (values:(cm_value)list)`,
          ann4,
          `tvm_iter 1
            (tvm_iter 1
              (tvm_iter 1
                (tvm_iter 1 (target:tvm_task))))`,
          `CMIntV 256i`, `256i:int`, suffix5),
          get_cm_target_push()), code4), sim4), capacity_sum),
        push_bridge);

    thm mod2_bridge = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_value_number_def(), fixed_256,
          get_tower_add_def(), get_tower_mod_def(),
          get_tower_wrap64_idempotent())),
        `tower_mod
           (cm_value_number (st:cm_src_state)
             ${sum_value:cm_value})
           (cm_value_number st (CMIntV 256i)) ==
         cm_value_number st ${final_value:cm_value}`));
    thm mod2 = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `CMIntV 256i`, sum_value,
        `values:(cm_value)list`, ann5,
        `tvm_iter 1
          (tvm_iter 1
            (tvm_iter 1
              (tvm_iter 1
                (tvm_iter 1 (target:tvm_task)))))`,
        `TVMModOp:tvm_opcode`, `tower_mod:int->int->int`,
        final_value, `rest:(tvm_inst)list`),
        get_cm_target_binary_nonzero());
    thm sim6 = match_mp_rule(match_mp_rule(match_mp_rule(
        match_mp_rule(match_mp_rule(mod2,
          get_tvm_mod_transition()), code5), sim5),
        eqf_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_value_number_def(), fixed_256)),
          `cm_value_number (st:cm_src_state) (CMIntV 256i) ==
           0i`))), mod2_bridge);

    thm arithmetic = mp_rule(
        spec_rule(number, cm_char_normalize_number),
        assume_rule(
          `tower_signed64
            (cm_value_number (st:cm_src_state) (v:cm_value))`));
    thm intermediate_number = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_value_number_def(), get_tower_mod_def(),
          get_tower_wrap64_idempotent())),
        `cm_value_number (st:cm_src_state)
           ${final_value:cm_value} ==
         ${final_number:int}`));
    thm converted_number = conv_rule(
        reduce_rewrite_conv(THM_LIST(is_char)),
        specl_rule(TERM_LIST(
          `st:cm_src_state`, `ty:cm_type`, `v:cm_value`),
          get_cm_convert_value_number_bridge()));
    thm number_equal = trans_rule(
        intermediate_number,
        trans_rule(arithmetic, sym_rule(converted_number)));
    thm revalued = match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          final_value,
          `cm_convert_value st (ty:cm_type) (v:cm_value)`,
          `values:(cm_value)list`, ann6,
          `tvm_iter 1
            (tvm_iter 1
              (tvm_iter 1
                (tvm_iter 1
                  (tvm_iter 1
                    (tvm_iter 1 (target:tvm_task))))))`),
          get_cm_target_revalue()), number_equal), sim6);

    term final_ann =
        `cm_ann_linear
          (cm_char_normalize_code (ty:cm_type))
          (ann:cm_annotation)`;
    thm pc_view = apply_conversion(
        reduce_rewrite_conv(code_rules),
        `cm_ann_pc ${final_ann:cm_annotation} ==
         cm_ann_pc ${ann6:cm_annotation}`);
    thm pc_normal = int_arith_rule(
        `cm_ann_pc (ann:cm_annotation) + 6i ==
         (((((cm_ann_pc ann + 1i) + 1i) + 1i) + 1i) + 1i) + 1i`);
    thm same_pc =
        eq_mp_rule(sym_rule(pc_view), pc_normal);
    thm same_calls = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(code_rules),
        `cm_ann_calls ${final_ann:cm_annotation} ==
         cm_ann_calls ${ann6:cm_annotation}`));
    thm same_spills = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(code_rules),
        `cm_ann_spills ${final_ann:cm_annotation} ==
         cm_ann_spills ${ann6:cm_annotation}`));
    thm same_saved = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(code_rules),
        `cm_ann_saved ${final_ann:cm_annotation} ==
         cm_ann_saved ${ann6:cm_annotation}`));
    term target6 =
        `tvm_iter 1
          (tvm_iter 1
            (tvm_iter 1
              (tvm_iter 1
                (tvm_iter 1
                  (tvm_iter 1 (target:tvm_task))))))`;
    thm reannotated = match_mp_rule(match_mp_rule(match_mp_rule(
        match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `cm_convert_value st CMCharTy (v:cm_value) ::
            (values:(cm_value)list)`,
          ann6, final_ann, target6),
          get_cm_target_reannotate()), same_pc), same_calls),
        same_spills), same_saved), revalued);

    thm num_of_int_six = spec_rule(
        `6:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM"));
    thm_list final_rules = (thm_list)vector_copy(code_rules);
    vector_add(&final_rules, cm_code_steps_def);
    vector_add(&final_rules, num_of_int_six);
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
        conv_rule(reduce_rewrite_conv(final_rules), reannotated);
    conv normalize = then_conv(
        then_conv(reduce_rewrite_conv(final_rules),
          rewrite_conv(THM_LIST(num_of_int_six))),
        reduce_rewrite_conv(final_rules));
    thm target_view =
        apply_conversion(normalize, goal_ccl(branch->g));
    ACCEPT_TAC(branch,
        eq_mp_rule(sym_rule(target_view), normalized));
  }

  {
    gnode branch = type_cases[1];
    thm not_char =
        assume_rule(`~((ty:cm_type) == CMCharTy)`);
    thm old_sim = assume_rule(
        `cm_running_target_sim (p:cm_program) (fid:int)
          (st:cm_src_state)
          ((v:cm_value) :: (values:(cm_value)list))
          (ann:cm_annotation) (target:tvm_task)`);
    thm converted_number = conv_rule(
        reduce_rewrite_conv(THM_LIST(not_char)),
        specl_rule(TERM_LIST(
          `st:cm_src_state`, `ty:cm_type`, `v:cm_value`),
          get_cm_convert_value_number_bridge()));
    thm revalued = match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `v:cm_value`,
          `cm_convert_value st (ty:cm_type) v`,
          `values:(cm_value)list`, `ann:cm_annotation`,
          `target:tvm_task`), get_cm_target_revalue()),
        sym_rule(converted_number)), old_sim);
    term final_ann =
        `cm_ann_linear
          (cm_char_normalize_code (ty:cm_type))
          (ann:cm_annotation)`;
    thm_list ann_rules = THM_LIST(
        get_cm_char_normalize_code_def(), not_char,
        cm_ann_linear_def, cm_ann_plain_def,
        cm_ann_pc_def, cm_ann_calls_def,
        cm_ann_spills_def, cm_ann_saved_def,
        get_theorem_by_name("ILENGTH_DEF"));
    thm pc_view = apply_conversion(
        reduce_rewrite_conv(ann_rules),
        `cm_ann_pc ${final_ann:cm_annotation} ==
         cm_ann_pc (ann:cm_annotation)`);
    thm same_pc = eq_mp_rule(sym_rule(pc_view),
        int_arith_rule(
          `cm_ann_pc (ann:cm_annotation) + 0i == cm_ann_pc ann`));
    thm same_calls = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(ann_rules),
        `cm_ann_calls ${final_ann:cm_annotation} ==
         cm_ann_calls (ann:cm_annotation)`));
    thm same_spills = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(ann_rules),
        `cm_ann_spills ${final_ann:cm_annotation} ==
         cm_ann_spills (ann:cm_annotation)`));
    thm same_saved = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(ann_rules),
        `cm_ann_saved ${final_ann:cm_annotation} ==
         cm_ann_saved (ann:cm_annotation)`));
    thm reannotated = match_mp_rule(match_mp_rule(match_mp_rule(
        match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `cm_convert_value st (ty:cm_type) v ::
            (values:(cm_value)list)`,
          `ann:cm_annotation`, final_ann, `target:tvm_task`),
          get_cm_target_reannotate()), same_pc), same_calls),
        same_spills), same_saved), revalued);
    thm num_of_int_zero = spec_rule(
        `0:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM"));
    thm_list count_rules = THM_LIST(
        get_cm_char_normalize_code_def(), not_char,
        cm_code_steps_def, get_theorem_by_name("APPEND"),
        get_theorem_by_name("ILENGTH_DEF"), num_of_int_zero);
    conv count_normalize = then_conv(
        then_conv(reduce_rewrite_conv(count_rules),
          rewrite_conv(THM_LIST(num_of_int_zero))),
        reduce_rewrite_conv(count_rules));
    thm zero_steps = eqt_elim_rule(apply_conversion(
        count_normalize,
        `cm_code_steps
           (cm_char_normalize_code (ty:cm_type)) == 0`));
    thm target_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          zero_steps, conjunct1_rule(get_tvm_iter_def()))),
        goal_ccl(branch->g));
    ACCEPT_TAC(branch,
        eq_mp_rule(sym_rule(target_view), reannotated));
  }
  return gnode_prove(root);
}

PROOF thm cm_target_char_normalize =
    cm_prove_target_char_normalize();

PROOF thm get_cm_target_char_normalize(void) {
  return cm_target_char_normalize;
}

PROOF static int cmc_preservation_target_convert_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_convert_axioms_before,
      "cmc_preservation_target_convert introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_convert_checks =
    cmc_preservation_target_convert_final_checks();
