#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_call_pending.h"

#require "cmc_preservation_call_pending_machine.c"
#require "cmc_preservation_target_call_fp.c"

PROOF static size_t _cmc_preservation_target_call_pending_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_target_call_pending(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (callee:int)
         (st:cm_src_state) (values:(cm_value)list)
         (ann:cm_annotation) (entered:cm_annotation)
         (target:tvm_task) (rest:(tvm_inst)list) (base:int).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst TVMStoreOp 0i ::
            TVMInst TVMPopOp 0i :: rest) ==>
         cm_running_target_sim p caller st
           (CMIntV 8i :: CMIntV base :: CMIntV base :: values)
           ann target ==>
         cm_function_wf p
           (inth callee (cm_program_functions p)) ==>
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         cm_state_tags_generation_below st
           (cm_state_nextgen st) ==>
         cm_values_generation_below (cm_state_nextgen st) values ==>
         cm_spill_frames_generation_below (cm_state_nextgen st)
           (cm_active_spill_frames caller st ann) ==>
         cm_tagged_span_valid st ==>
         (!addr.
            cm_live_address st addr ==>
            ~(base <= addr && addr < base + 8i)) ==>
         (!addr.
            cm_live_address st addr ==>
            ~(8i <= addr && addr < 8i + 8i)) ==>
         cm_call_frames_store_safe CMIntTy 8i
           (cm_ann_calls ann) ==>
         cm_spill_frames_store_safe p CMIntTy 8i
           (cm_active_spill_frames caller st ann) ==>
         base == cm_state_fp st -
           cm_frame_size (cm_program_structs p)
             (inth callee (cm_program_functions p)) ==>
         tower_signed64 (cm_state_fp st) ==>
         tower_signed64 base ==>
         cm_ann_pc entered == cm_ann_pc ann + 2i ==>
         cm_ann_calls entered == cm_ann_calls ann ==>
         cm_active_spill_frames callee
           (cm_call_pending_base p callee st) entered ==
           CMSpillFrame callee base [] ::
             cm_active_spill_frames caller st ann ==>
         cm_running_target_sim p callee
           (cm_call_pending_base p callee st) values entered
           (tvm_iter 2 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term pending =
      `cm_call_pending_base (p:cm_program) (callee:int)
        (st:cm_src_state)`;
  term middle =
      `cm_ann_plain (cm_ann_pc (ann:cm_annotation) + 1i)
        (cm_ann_temp (entered:cm_annotation))
        (cm_ann_break entered) (cm_ann_continue entered) entered`;
  term next =
      `tvm_next_state (vm:tvm_state)
        (TL (TL (tvm_stack vm))) (tvm_calls vm)
        (tower_setw (tvm_mem vm) 8i (base:int))
        (tvm_input vm) (tvm_output vm)`;

  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMStoreOp 0i ::
         TVMInst TVMPopOp 0i :: (rest:(tvm_inst)list))`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (caller:int)
        (st:cm_src_state)
        (CMIntV 8i :: CMIntV (base:int) :: CMIntV base ::
          (values:(cm_value)list))
        (ann:cm_annotation) (target:tvm_task)`);
  thm expanded = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_running_target_sim_def)),
      concl(running)), running);
  thm body = assume_rule(
      `(target:tvm_task) ==
          TVMRunTask (cm_compile_model (p:cm_program)) (vm:tvm_state) &&
       tvm_pc vm == cm_ann_pc (ann:cm_annotation) &&
       cm_machine_state_sim p (st:cm_src_state) vm
         (cm_ann_calls ann)
         (cm_active_spill_frames (caller:int) st ann)
         (CMIntV 8i :: CMIntV (base:int) :: CMIntV base ::
           (values:(cm_value)list) ) []`);
  thm target_equal = conjunct1_rule(body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(body));
  thm machine = conjunct2_rule(conjunct2_rule(body));

  thm stack_length = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (caller:int) st ann`,
      `CMIntV 8i :: CMIntV (base:int) :: CMIntV base ::
        (values:(cm_value)list)`, `[]:(int)list`),
      get_cm_machine_sim_stack_length()), machine);
  thm nonnegative = ispec_rule(`values:(cm_value)list`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  thm stack_two = mp_rule(mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) ==
         (1i + 1i + 1i + ilength (values:(cm_value)list)) + 0i ==>
       0i <= ilength values ==>
       2i <= ilength (tvm_stack vm)`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length)),
      nonnegative);
  thm stack_shape = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (caller:int) st ann`,
      `CMIntV 8i :: CMIntV (base:int) :: CMIntV base ::
        (values:(cm_value)list)`, `[]:(int)list`),
      get_cm_machine_sim_stack_shape()), machine);
  thm stack_head = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(stack_shape, cm_encode_values_def,
        get_cm_value_number_def(), get_tower_wrap64_def(),
        get_theorem_by_name("APPEND"), get_theorem_by_name("HD"))),
      `HD (tvm_stack (vm:tvm_state)) == 8i`));
  thm fixed_base = mp_rule(spec_rule(`base:int`,
      get_tower_wrap64_fixed()),
      assume_rule(`tower_signed64 (base:int)`));
  thm stack_second = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(stack_shape, cm_encode_values_def,
        get_cm_value_number_def(), fixed_base,
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
      `HD (TL (tvm_stack (vm:tvm_state))) == (base:int)`));
  thm address_ok = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_tower_word_valid_def())),
      `tower_word_valid 8i`));
  thm action = specl_rule(TERM_LIST(
      `tvm_object_code (cm_compile_model (p:cm_program))`,
      `0i:int`, `vm:tvm_state`), get_tvm_store_transition());
  action = conv_rule(reduce_rewrite_conv(THM_LIST(
      stack_two, stack_head, stack_second, address_ok)), action);
  thm compiled_code = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (tvm_pc (vm:tvm_state))
        (TVMInst TVMStoreOp 0i ::
         TVMInst TVMPopOp 0i :: (rest:(tvm_inst)list))`));
  thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
      `TVMStoreOp:tvm_opcode`, `0i:int`,
      `TVMInst TVMPopOp 0i :: (rest:(tvm_inst)list)`, next),
      cm_tvm_state_iter_one), compiled_code), action);
  stepped = conv_rule(rewrite_conv(THM_LIST(sym_rule(target_equal))),
      stepped);

  thm machine_after = machine;
  machine_after = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `caller:int`, `callee:int`,
      `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (caller:int) st ann`,
      `values:(cm_value)list`, `base:int`),
      get_cm_machine_call_pending_store()), machine_after);
  machine_after = match_mp_rule(machine_after, assume_rule(
      `cm_function_wf (p:cm_program)
        (inth (callee:int) (cm_program_functions p))`));
  machine_after = match_mp_rule(machine_after, assume_rule(
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`));
  machine_after = match_mp_rule(machine_after, assume_rule(
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`));
  machine_after = match_mp_rule(machine_after, assume_rule(
      `cm_values_generation_below (cm_state_nextgen st)
        (values:(cm_value)list)`));
  machine_after = match_mp_rule(machine_after, assume_rule(
      `cm_spill_frames_generation_below (cm_state_nextgen st)
        (cm_active_spill_frames (caller:int) st ann)`));
  machine_after = match_mp_rule(machine_after,
      assume_rule(`cm_tagged_span_valid (st:cm_src_state)`));
  machine_after = match_mp_rule(machine_after, assume_rule(
      `!addr.
         cm_live_address (st:cm_src_state) addr ==>
         ~((base:int) <= addr && addr < base + 8i)`));
  machine_after = match_mp_rule(machine_after, assume_rule(
      `!addr.
         cm_live_address (st:cm_src_state) addr ==>
         ~((8i <= addr && addr < 8i + 8i))`));
  machine_after = match_mp_rule(machine_after, assume_rule(
      `cm_call_frames_store_safe CMIntTy 8i
        (cm_ann_calls (ann:cm_annotation))`));
  machine_after = match_mp_rule(machine_after, assume_rule(
      `cm_spill_frames_store_safe (p:cm_program) CMIntTy 8i
        (cm_active_spill_frames (caller:int) st ann)`));
  machine_after = match_mp_rule(machine_after, assume_rule(
      `(base:int) == cm_state_fp (st:cm_src_state) -
        cm_frame_size (cm_program_structs (p:cm_program))
          (inth (callee:int) (cm_program_functions p))`));
  machine_after = match_mp_rule(machine_after, assume_rule(
      `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  machine_after = match_mp_rule(machine_after,
      assume_rule(`tower_signed64 (base:int)`));

  thm next_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_tvm_next_state_def(), get_tvm_state_selectors_def(),
        cm_ann_plain_def, cm_ann_pc_def, pc_equal)),
      `tvm_pc ${next:tvm_state} == cm_ann_pc ${middle:cm_annotation}`));
  thm calls_equal = assume_rule(
      `cm_ann_calls (entered:cm_annotation) ==
       cm_ann_calls (ann:cm_annotation)`);
  thm active_equal = assume_rule(
      `cm_active_spill_frames (callee:int) ${pending:cm_src_state}
        (entered:cm_annotation) ==
       CMSpillFrame callee (base:int) [] ::
         cm_active_spill_frames (caller:int) st ann`);
  thm middle_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_plain_def, cm_ann_pc_def)),
      `cm_ann_pc ${middle:cm_annotation} ==
       cm_ann_pc (ann:cm_annotation) + 1i`));
  thm middle_calls_entered = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_plain_def, cm_ann_calls_def)),
      `cm_ann_calls ${middle:cm_annotation} ==
       cm_ann_calls (entered:cm_annotation)`));
  thm middle_calls = trans_rule(middle_calls_entered, calls_equal);
  thm middle_active_entered = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_plain_def, cm_ann_spills_def, cm_ann_saved_def,
        cm_active_spill_frames_def)),
      `cm_active_spill_frames (callee:int) ${pending:cm_src_state}
         ${middle:cm_annotation} ==
       cm_active_spill_frames callee ${pending:cm_src_state}
         (entered:cm_annotation)`));
  thm middle_active =
      trans_rule(middle_active_entered, active_equal);
  thm_list middle_rules =
      THM_LIST(middle_pc, middle_calls, middle_active);
  thm middle_machine = conv_rule(
      reduce_rewrite_conv(middle_rules), machine_after);
  term middle_body =
      `tvm_iter 1 (target:tvm_task) ==
         TVMRunTask (cm_compile_model (p:cm_program)) ${next:tvm_state} &&
       tvm_pc ${next:tvm_state} == cm_ann_pc ${middle:cm_annotation} &&
       cm_machine_state_sim p ${pending:cm_src_state} ${next:tvm_state}
         (cm_ann_calls ${middle:cm_annotation})
         (cm_active_spill_frames (callee:int) ${pending:cm_src_state}
           ${middle:cm_annotation})
         (CMIntV (base:int) :: (values:(cm_value)list)) []`;
  thm assembled_middle = conj_rule(stepped,
      conj_rule(next_pc, middle_machine));
  thm middle_body_view = apply_conversion(
      reduce_rewrite_conv(middle_rules), middle_body);
  thm middle_body_exact = eq_mp_rule(sym_rule(middle_body_view),
      conv_rule(reduce_rewrite_conv(middle_rules), assembled_middle));
  term middle_exists =
      `?next_vm.
         tvm_iter 1 (target:tvm_task) ==
           TVMRunTask (cm_compile_model (p:cm_program)) next_vm &&
         tvm_pc next_vm == cm_ann_pc ${middle:cm_annotation} &&
         cm_machine_state_sim p ${pending:cm_src_state} next_vm
           (cm_ann_calls ${middle:cm_annotation})
           (cm_active_spill_frames (callee:int) ${pending:cm_src_state}
             ${middle:cm_annotation})
           (CMIntV (base:int) :: (values:(cm_value)list)) []`;
  thm middle_witness = exists_rule(middle_exists, next,
      middle_body_exact);
  thm middle_running = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_running_target_sim_def)),
      `cm_running_target_sim (p:cm_program) (callee:int)
        ${pending:cm_src_state}
        (CMIntV (base:int) :: (values:(cm_value)list))
        ${middle:cm_annotation} (tvm_iter 1 (target:tvm_task))`)),
      middle_witness);
  middle_running = choose_rule(`vm:tvm_state`, expanded,
      middle_running);

  thm_list code_rules = THM_LIST(
      cm_ann_plain_def, cm_ann_pc_def,
      get_theorem_by_name("ILENGTH_DEF"));
  thm tail_rule = ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`,
      `cm_ann_pc (ann:cm_annotation)`,
      `[TVMInst TVMStoreOp 0i]:(tvm_inst)list`,
      `TVMInst TVMPopOp 0i :: (rest:(tvm_inst)list)`),
      get_cm_code_at_append_right());
  thm tail = mp_rule(
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND"))), tail_rule), code_at);
  tail = conv_rule(reduce_rewrite_conv(code_rules), tail);
  thm tail_bridge = beta_norm(ap_term_rule(
      `\pc:int.
         cm_code_at (cm_model_code (p:cm_program)) pc
           (TVMInst TVMPopOp 0i :: (rest:(tvm_inst)list))`,
      sym_rule(middle_pc)));
  tail = eq_mp_rule(tail_bridge, tail);
  thm popped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `callee:int`, pending,
      `CMIntV (base:int):cm_value`, `values:(cm_value)list`,
      middle, `tvm_iter 1 (target:tvm_task)`,
      `rest:(tvm_inst)list`), get_cm_target_pop()), tail),
      middle_running);

  term after_pop =
      `cm_ann_linear [TVMInst TVMPopOp 0i]
        ${middle:cm_annotation}`;
  thm entered_pc = assume_rule(
      `cm_ann_pc (entered:cm_annotation) ==
       cm_ann_pc (ann:cm_annotation) + 2i`);
  thm pc_arith = int_ring_rule(
      `!(pc:int). pc + 2i == (pc + 1i) + 1i`);
  thm_list annotation_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def,
      get_theorem_by_name("ILENGTH_DEF"), entered_pc, pc_arith);
  term selectors =
      `cm_ann_pc (entered:cm_annotation) ==
         cm_ann_pc ${after_pop:cm_annotation} &&
       cm_ann_calls entered == cm_ann_calls ${after_pop:cm_annotation} &&
       cm_ann_spills entered == cm_ann_spills ${after_pop:cm_annotation} &&
       cm_ann_saved entered == cm_ann_saved ${after_pop:cm_annotation}`;
  thm selector_facts = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(annotation_rules), selectors));
  thm reannotated = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `callee:int`, pending,
        `values:(cm_value)list`, after_pop, `entered:cm_annotation`,
        `tvm_iter 1 (tvm_iter 1 (target:tvm_task))`),
        get_cm_target_reannotate()),
      conjunct1_rule(selector_facts)),
      conjunct1_rule(conjunct2_rule(selector_facts))),
      conjunct1_rule(conjunct2_rule(conjunct2_rule(selector_facts)))),
      conjunct2_rule(conjunct2_rule(conjunct2_rule(selector_facts)))),
      popped);
  thm iter_two = specl_rule(TERM_LIST(
      `1:num`, `1:num`, `target:tvm_task`), get_cm_tvm_iter_add());
  reannotated = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(iter_two),
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `(1:num) + 1`))), reannotated);
  ACCEPT_TAC(leaf, reannotated);
  return gnode_prove(root);
}
PROOF thm cm_target_call_pending =
    cm_prove_target_call_pending();

PROOF thm get_cm_target_call_pending(void) {
  return cm_target_call_pending;
}

PROOF static int cmc_preservation_target_call_pending_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_call_pending_axioms_before,
      "cmc_preservation_target_call_pending introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_call_pending)) == 0,
      "cm_target_call_pending has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_call_pending_checks =
    cmc_preservation_target_call_pending_final_checks();
