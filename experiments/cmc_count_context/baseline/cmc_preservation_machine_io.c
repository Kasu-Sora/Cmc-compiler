#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_machine_ops.h"
#require "cmc_preservation_machine_ops.c"
#include "cmc_preservation_machine_io.h"

PROOF static size_t _cmc_preservation_machine_io_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_value_number_state_io(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (input:(int)list) (output:(int)list)
         (v:cm_value).
         cm_value_number (cm_state_io st input output) v ==
         cm_value_number st v`);
  gnode with_state = GEN_TAC(root, "st");
  gnode with_input = GEN_TAC(with_state, "input");
  gnode with_output = GEN_TAC(with_input, "output");
  gnode_list cases = INDUCT_TAC(with_output, `v:cm_value`);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_value_number_def());
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_TAC(leaf, reduce_rewrite_conv(rules));
  }
  return gnode_prove(root);
}
PROOF thm cm_value_number_state_io =
    cm_prove_value_number_state_io();

PROOF static thm cm_prove_encode_values_state_io(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (input:(int)list) (output:(int)list)
         (values:(cm_value)list).
         cm_encode_values (cm_state_io st input output) values ==
         cm_encode_values st values`);
  gnode with_state = GEN_TAC(root, "st");
  gnode with_input = GEN_TAC(with_state, "input");
  gnode with_output = GEN_TAC(with_input, "output");
  gnode_list cases = INDUCT_TAC(with_output, `values:(cm_value)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        cm_encode_values_def, cm_value_number_state_io));
  }
  return gnode_prove(root);
}
PROOF thm cm_encode_values_state_io =
    cm_prove_encode_values_state_io();

PROOF static thm cm_prove_initialized_bytes_state_io(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (input:(int)list) (output:(int)list)
         (vmem:int->int).
         cm_initialized_bytes_sim (cm_state_io st input output) vmem <=>
         cm_initialized_bytes_sim st vmem`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, cm_initialized_bytes_sim_def);
  vector_add(&rules, cm_live_address_def);
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF static thm cm_initialized_bytes_state_io =
    cm_prove_initialized_bytes_state_io();

PROOF static thm cm_prove_stored_provenance_state_io(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (input:(int)list) (output:(int)list)
         (vmem:int->int).
         cm_stored_provenance_sim (cm_state_io st input output) vmem <=>
         cm_stored_provenance_sim st vmem`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, cm_stored_provenance_sim_def);
  vector_add(&rules, cm_value_number_state_io);
  vector_add(&rules, cm_live_address_def);
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF static thm cm_stored_provenance_state_io =
    cm_prove_stored_provenance_state_io();

PROOF static thm cm_prove_spill_list_state_io(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (input:(int)list)
         (output:(int)list) (vmem:int->int) (fid:int) (fp:int)
         (spills:(cm_spill)list).
         cm_spill_list_sim p (cm_state_io st input output) vmem
           fid fp spills <=>
         cm_spill_list_sim p st vmem fid fp spills`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_state = GEN_TAC(with_program, "st");
  gnode with_input = GEN_TAC(with_state, "input");
  gnode with_output = GEN_TAC(with_input, "output");
  gnode with_mem = GEN_TAC(with_output, "vmem");
  gnode with_fid = GEN_TAC(with_mem, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode_list cases = INDUCT_TAC(with_fp, `spills:(cm_spill)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        cm_spill_list_sim_def, cm_value_number_state_io));
  }
  return gnode_prove(root);
}
PROOF static thm cm_spill_list_state_io =
    cm_prove_spill_list_state_io();

PROOF static thm cm_prove_spill_frames_state_io(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (input:(int)list)
         (output:(int)list) (vmem:int->int)
         (frames:(cm_spill_frame)list).
         cm_spill_frames_sim p (cm_state_io st input output) vmem
           frames <=>
         cm_spill_frames_sim p st vmem frames`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_state = GEN_TAC(with_program, "st");
  gnode with_input = GEN_TAC(with_state, "input");
  gnode with_output = GEN_TAC(with_input, "output");
  gnode with_mem = GEN_TAC(with_output, "vmem");
  gnode_list cases =
      INDUCT_TAC(with_mem, `frames:(cm_spill_frame)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        cm_spill_frames_sim_def, cm_spill_list_state_io));
  }
  return gnode_prove(root);
}
PROOF static thm cm_spill_frames_state_io =
    cm_prove_spill_frames_state_io();

PROOF static thm cm_prove_machine_io_restack(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (old_values:(cm_value)list) (new_values:(cm_value)list)
         (suffix:(int)list) (input:(int)list) (output:(int)list)
         (pc:int) (new_stack:(int)list).
         cm_machine_state_sim p st target frames spill_frames
           old_values suffix ==>
         new_stack ==
           cm_encode_values (cm_state_io st input output) new_values ++
           suffix ==>
         cm_machine_state_sim p (cm_state_io st input output)
           (TVMState pc new_stack (tvm_calls target) (tvm_mem target)
             input output)
           frames spill_frames new_values suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (old_values:(cm_value)list) (suffix:(int)list)`);
  thm parts = conv_rule(rewrite_conv(THM_LIST(cm_machine_sim_parts)),
      simulation);
  thm initialized = conjunct1_rule(parts);
  thm after_initialized = conjunct2_rule(parts);
  thm provenance = conjunct1_rule(after_initialized);
  thm after_provenance = conjunct2_rule(after_initialized);
  thm fp = conjunct1_rule(after_provenance);
  thm after_fp = conjunct2_rule(after_provenance);
  thm calls = conjunct1_rule(after_fp);
  thm after_calls = conjunct2_rule(after_fp);
  thm spills = conjunct1_rule(after_calls);
  thm after_spills = conjunct2_rule(after_calls);
  thm stack_equal = assume_rule(
      `(new_stack:(int)list) ==
       cm_encode_values
         (cm_state_io (st:cm_src_state) (input:(int)list)
           (output:(int)list))
         (new_values:(cm_value)list) ++ (suffix:(int)list)`);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, cm_machine_sim_parts);
  vector_add(&rules, get_tvm_state_selectors_def());
  vector_add(&rules, cm_initialized_bytes_state_io);
  vector_add(&rules, cm_stored_provenance_state_io);
  vector_add(&rules, cm_spill_frames_state_io);
  vector_add(&rules, cm_operand_suffix_sim_def);
  vector_add(&rules, cm_encode_values_state_io);
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  thm result = conj_rule(initialized,
      conj_rule(provenance,
      conj_rule(fp,
      conj_rule(calls,
      conj_rule(spills,
      conj_rule(refl_rule(`input:(int)list`),
      conj_rule(refl_rule(`output:(int)list`), stack_equal)))))));
  ACCEPT_TAC(opened, conv_rule(reduce_rewrite_conv(rules), result));
  return gnode_prove(root);
}
PROOF thm cm_machine_io_restack = cm_prove_machine_io_restack();

PROOF static thm cm_prove_machine_getc_empty(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (values:(cm_value)list) (suffix:(int)list).
         cm_machine_state_sim p st target frames spill_frames
           values suffix ==>
         cm_state_input st == [] ==>
         cm_machine_state_sim p st
           (tvm_next_state target ((--1i) :: tvm_stack target)
             (tvm_calls target) (tvm_mem target)
             (tvm_input target) (tvm_output target))
           frames spill_frames ((CMIntV (--1i)) :: values) suffix`);
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
        shape, cm_encode_values_def, get_cm_value_number_def(),
        get_tower_wrap64_def(), get_theorem_by_name("APPEND"))),
      `(--1i) :: tvm_stack (target:tvm_state) ==
       cm_encode_values (st:cm_src_state)
         ((CMIntV (--1i)) :: (values:(cm_value)list)) ++
       (suffix:(int)list)`));
  thm result = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `values:(cm_value)list`, `(CMIntV (--1i)) :: values`,
      `suffix:(int)list`, `tvm_pc (target:tvm_state) + 1i`,
      `(--1i) :: tvm_stack target`), cm_machine_sim_restack),
      simulation), stack);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(get_tvm_next_state_def())));
  ACCEPT_TAC(opened, result);
  return gnode_prove(root);
}
PROOF thm cm_machine_getc_empty = cm_prove_machine_getc_empty();

PROOF static thm cm_prove_machine_getc_nonempty(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (values:(cm_value)list) (suffix:(int)list).
         cm_machine_state_sim p st target frames spill_frames
           values suffix ==>
         ~(cm_state_input st == []) ==>
         tower_byte_value (HD (cm_state_input st)) ==>
         cm_machine_state_sim p
           (cm_state_io st (TL (cm_state_input st))
             (cm_state_output st))
           (tvm_next_state target
             (tower_u8 (HD (tvm_input target)) :: tvm_stack target)
             (tvm_calls target) (tvm_mem target)
             (TL (tvm_input target)) (tvm_output target))
           frames spill_frames
           ((CMIntV (HD (cm_state_input st))) :: values) suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (values:(cm_value)list) (suffix:(int)list)`);
  thm io = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `values:(cm_value)list`, `suffix:(int)list`),
      cm_machine_sim_io), simulation);
  thm shape = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `values:(cm_value)list`, `suffix:(int)list`),
      cm_machine_sim_stack_shape), simulation);
  thm byte = assume_rule(
      `tower_byte_value (HD (cm_state_input (st:cm_src_state)))`);
  thm u8_fixed = mp_rule(spec_rule(
      `HD (cm_state_input (st:cm_src_state))`,
      get_tower_u8_fixed()), byte);
  thm bounds = conv_rule(rewrite_conv(THM_LIST(
      get_tower_byte_value_def())), byte);
  thm signed_bounds = mp_rule(int_arith_rule(
      `0i <= HD (cm_state_input (st:cm_src_state)) &&
       HD (cm_state_input st) < 256i ==>
       --9223372036854775808i <= HD (cm_state_input st) &&
       HD (cm_state_input st) <= 9223372036854775807i`), bounds);
  thm signed_expansion = apply_conversion(
      rewrite_conv(THM_LIST(get_tower_signed64_def())),
      `tower_signed64 (HD
         (cm_state_input (st:cm_src_state)))`);
  thm signed_range =
      eq_mp_rule(sym_rule(signed_expansion), signed_bounds);
  thm wrap_fixed = mp_rule(spec_rule(
      `HD (cm_state_input (st:cm_src_state))`,
      get_tower_wrap64_fixed()), signed_range);
  thm byte_equal = trans_rule(u8_fixed, sym_rule(wrap_fixed));
  thm stack = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        shape, byte_equal, cm_encode_values_def,
        cm_encode_values_state_io, cm_value_number_state_io,
        get_cm_value_number_def(), get_theorem_by_name("APPEND"))),
      `tower_u8 (HD (cm_state_input (st:cm_src_state))) ::
         tvm_stack (target:tvm_state) ==
       cm_encode_values
         (cm_state_io st (TL (cm_state_input st))
           (cm_state_output st))
         ((CMIntV (HD (cm_state_input st))) ::
           (values:(cm_value)list)) ++
       (suffix:(int)list)`));
  thm result = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `values:(cm_value)list`,
      `(CMIntV (HD (cm_state_input st))) :: values`,
      `suffix:(int)list`, `TL (cm_state_input st)`,
      `cm_state_output st`, `tvm_pc (target:tvm_state) + 1i`,
      `tower_u8 (HD (cm_state_input st)) :: tvm_stack target`),
      cm_machine_io_restack), simulation), stack);
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_tvm_next_state_def(), conjunct1_rule(io),
      conjunct2_rule(io))));
  ACCEPT_TAC(opened, result);
  return gnode_prove(root);
}
PROOF thm cm_machine_getc_nonempty =
    cm_prove_machine_getc_nonempty();

PROOF static thm cm_prove_machine_putc(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (v:cm_value) (values:(cm_value)list) (suffix:(int)list).
         cm_machine_state_sim p st target frames spill_frames
           (v :: v :: values) suffix ==>
         cm_machine_state_sim p
           (cm_state_io st (cm_state_input st)
             (cm_state_output st ++
              [tower_u8 (cm_value_number st v)]))
           (tvm_next_state target (TL (tvm_stack target))
             (tvm_calls target) (tvm_mem target)
             (tvm_input target)
             (tvm_output target ++
              [tower_u8 (HD (tvm_stack target))]))
           frames spill_frames
           ((CMIntV (cm_value_number st v)) :: values) suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         ((v:cm_value) :: v :: (values:(cm_value)list))
         (suffix:(int)list)`);
  thm io = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `(v:cm_value) :: v :: (values:(cm_value)list)`,
      `suffix:(int)list`), cm_machine_sim_io), simulation);
  thm head = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`, `v:cm_value`,
      `(v:cm_value) :: (values:(cm_value)list)`,
      `suffix:(int)list`), cm_machine_sim_stack_head), simulation);
  thm signed_range = specl_rule(TERM_LIST(
      `st:cm_src_state`, `v:cm_value`),
      get_cm_value_number_signed_bridge());
  thm fixed = mp_rule(spec_rule(
      `cm_value_number (st:cm_src_state) (v:cm_value)`,
      get_tower_wrap64_fixed()), signed_range);
  thm stack = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        conjunct2_rule(head), cm_encode_values_def,
        cm_encode_values_state_io, cm_value_number_state_io,
        get_cm_value_number_def(), fixed,
        get_theorem_by_name("APPEND"))),
      `TL (tvm_stack (target:tvm_state)) ==
       cm_encode_values
         (cm_state_io (st:cm_src_state) (cm_state_input st)
           (cm_state_output st ++
            [tower_u8 (cm_value_number st (v:cm_value))]))
         ((CMIntV (cm_value_number st v)) ::
           (values:(cm_value)list)) ++
       (suffix:(int)list)`));
  thm result = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `(v:cm_value) :: v :: (values:(cm_value)list)`,
      `(CMIntV (cm_value_number st v)) :: values`,
      `suffix:(int)list`, `cm_state_input st`,
      `cm_state_output st ++ [tower_u8 (cm_value_number st v)]`,
      `tvm_pc (target:tvm_state) + 1i`,
      `TL (tvm_stack target)`), cm_machine_io_restack),
      simulation), stack);
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_tvm_next_state_def(), conjunct1_rule(io),
      conjunct2_rule(io), conjunct1_rule(head))));
  ACCEPT_TAC(opened, result);
  return gnode_prove(root);
}
PROOF thm cm_machine_putc = cm_prove_machine_putc();

PROOF static thm cm_prove_machine_puti(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (v:cm_value) (values:(cm_value)list) (suffix:(int)list).
         cm_machine_state_sim p st target frames spill_frames
           (v :: v :: values) suffix ==>
         cm_machine_state_sim p
           (cm_state_io st (cm_state_input st)
             (cm_state_output st ++
              tower_decimal (cm_value_number st v)))
           (tvm_next_state target (TL (tvm_stack target))
             (tvm_calls target) (tvm_mem target)
             (tvm_input target)
             (tvm_output target ++
              tower_decimal (HD (tvm_stack target))))
           frames spill_frames
           ((CMIntV (cm_value_number st v)) :: values) suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         ((v:cm_value) :: v :: (values:(cm_value)list))
         (suffix:(int)list)`);
  thm io = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `(v:cm_value) :: v :: (values:(cm_value)list)`,
      `suffix:(int)list`), cm_machine_sim_io), simulation);
  thm head = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`, `v:cm_value`,
      `(v:cm_value) :: (values:(cm_value)list)`,
      `suffix:(int)list`), cm_machine_sim_stack_head), simulation);
  thm signed_range = specl_rule(TERM_LIST(
      `st:cm_src_state`, `v:cm_value`),
      get_cm_value_number_signed_bridge());
  thm fixed = mp_rule(spec_rule(
      `cm_value_number (st:cm_src_state) (v:cm_value)`,
      get_tower_wrap64_fixed()), signed_range);
  thm stack = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        conjunct2_rule(head), cm_encode_values_def,
        cm_encode_values_state_io, cm_value_number_state_io,
        get_cm_value_number_def(), fixed,
        get_theorem_by_name("APPEND"))),
      `TL (tvm_stack (target:tvm_state)) ==
       cm_encode_values
         (cm_state_io (st:cm_src_state) (cm_state_input st)
           (cm_state_output st ++
            tower_decimal (cm_value_number st (v:cm_value))))
         ((CMIntV (cm_value_number st v)) ::
           (values:(cm_value)list)) ++
       (suffix:(int)list)`));
  thm result = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `target:tvm_state`,
      `frames:(cm_call_sim_frame)list`,
      `spill_frames:(cm_spill_frame)list`,
      `(v:cm_value) :: v :: (values:(cm_value)list)`,
      `(CMIntV (cm_value_number st v)) :: values`,
      `suffix:(int)list`, `cm_state_input st`,
      `cm_state_output st ++ tower_decimal (cm_value_number st v)`,
      `tvm_pc (target:tvm_state) + 1i`,
      `TL (tvm_stack target)`), cm_machine_io_restack),
      simulation), stack);
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_tvm_next_state_def(), conjunct1_rule(io),
      conjunct2_rule(io), conjunct1_rule(head))));
  ACCEPT_TAC(opened, result);
  return gnode_prove(root);
}
PROOF thm cm_machine_puti = cm_prove_machine_puti();

PROOF thm get_cm_value_number_state_io(void) {
  return cm_value_number_state_io;
}
PROOF thm get_cm_encode_values_state_io(void) {
  return cm_encode_values_state_io;
}
PROOF thm get_cm_machine_io_restack(void) {
  return cm_machine_io_restack;
}
PROOF thm get_cm_machine_getc_empty(void) {
  return cm_machine_getc_empty;
}
PROOF thm get_cm_machine_getc_nonempty(void) {
  return cm_machine_getc_nonempty;
}
PROOF thm get_cm_machine_putc(void) { return cm_machine_putc; }
PROOF thm get_cm_machine_puti(void) { return cm_machine_puti; }

PROOF static int cmc_preservation_machine_io_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_machine_io_axioms_before,
      "cmc_preservation_machine_io introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_machine_io_checks =
    cmc_preservation_machine_io_final_checks();
