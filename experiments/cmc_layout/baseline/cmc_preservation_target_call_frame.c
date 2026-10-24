#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_call_frame.h"

#require "cmc_preservation_target_call_jump.c"
#require "cmc_preservation_machine_store.c"

PROOF static size_t _cmc_preservation_target_call_frame_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_rebase_call_frames_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!base.
        cm_rebase_call_frames (base:int)
          ([]:(cm_call_sim_frame)list) = []) &&
     (!base frame rest.
        cm_rebase_call_frames (base:int)
          ((frame:cm_call_sim_frame) ::
            (rest:(cm_call_sim_frame)list)) =
        CMCallSimFrame base (cm_call_sim_saved frame)
          (cm_call_sim_return frame) :: rest)`);

PROOF thm cm_ann_call_rebase_def = new_fun_definition(
    `cm_ann_call_rebase (base:int) (ann:cm_annotation) : cm_annotation =
       CMAnnotation (cm_ann_pc ann) (cm_ann_temp ann)
         (cm_ann_break ann) (cm_ann_continue ann)
         (cm_ann_cursors ann) (cm_ann_spills ann)
         (cm_ann_saved ann)
         (cm_rebase_call_frames base (cm_ann_calls ann))`);

PROOF static thm cm_prove_machine_call_save(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (base:int) (values:(cm_value)list) (suffix:(int)list).
         cm_machine_state_sim p st target frames spill_frames
           (CMIntV base :: CMIntV (cm_state_fp st) :: values) suffix ==>
         ~(frames == []) ==>
         cm_call_sim_base (HD frames) == 8i ==>
         cm_call_sim_saved (HD frames) == cm_state_fp st ==>
         cm_tagged_span_valid st ==>
         (!addr.
            cm_live_address st addr ==>
            ~(base <= addr && addr < base + 8i)) ==>
         cm_range_disjoint base 8i 8i 8i ==>
         cm_call_frames_store_safe CMIntTy base (TL frames) ==>
         cm_spill_frames_store_safe p CMIntTy base spill_frames ==>
         tower_signed64 (cm_state_fp st) ==>
         cm_machine_state_sim p st
           (tvm_next_state target (TL (TL (tvm_stack target)))
             (tvm_calls target)
             (tower_setw (tvm_mem target) base (cm_state_fp st))
             (tvm_input target) (tvm_output target))
           (cm_rebase_call_frames base frames)
           spill_frames values suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (CMIntV (base:int) :: CMIntV (cm_state_fp st) ::
           (values:(cm_value)list)) (suffix:(int)list)`);
  thm parts = conv_rule(rewrite_conv(THM_LIST(
      cm_machine_sim_parts)), simulation);
  thm initialized = conjunct1_rule(parts);
  thm after_initialized = conjunct2_rule(parts);
  thm provenance = conjunct1_rule(after_initialized);
  thm after_provenance = conjunct2_rule(after_initialized);
  thm fp_word = conjunct1_rule(after_provenance);
  thm after_fp = conjunct2_rule(after_provenance);
  thm calls = conjunct1_rule(after_fp);
  thm after_calls = conjunct2_rule(after_fp);
  thm spills = conjunct1_rule(after_calls);
  thm after_spills = conjunct2_rule(after_calls);
  thm input_equal = conjunct1_rule(after_spills);
  thm after_input = conjunct2_rule(after_spills);
  thm output_equal = conjunct1_rule(after_input);
  thm operand = conjunct2_rule(after_input);
  thm number_signed = assume_rule(
      `tower_signed64 (cm_state_fp (st:cm_src_state))`);
  thm number_fixed = mp_rule(spec_rule(
      `cm_state_fp (st:cm_src_state)`, get_tower_wrap64_fixed()),
      number_signed);
  thm new_initialized = mp_rule(mp_rule(mp_rule(
      specl_rule(TERM_LIST(
        `st:cm_src_state`, `tvm_mem (target:tvm_state)`,
        `base:int`, `cm_state_fp (st:cm_src_state)`),
        get_cm_initialized_scratch_store_sim()),
      initialized), number_signed), assume_rule(
        `!addr.
           cm_live_address (st:cm_src_state) addr ==>
           ~((base:int) <= addr && addr < base + 8i)`));
  thm new_provenance = mp_rule(mp_rule(mp_rule(mp_rule(
      specl_rule(TERM_LIST(
        `st:cm_src_state`, `tvm_mem (target:tvm_state)`,
        `base:int`, `cm_state_fp (st:cm_src_state)`),
        get_cm_provenance_scratch_store_sim()),
      provenance), number_signed), assume_rule(
        `cm_tagged_span_valid (st:cm_src_state)`)), assume_rule(
        `!addr.
           cm_live_address (st:cm_src_state) addr ==>
           ~((base:int) <= addr && addr < base + 8i)`));
  thm fp_unchanged = specl_rule(TERM_LIST(
      `CMIntTy:cm_type`, `base:int`,
      `cm_state_fp (st:cm_src_state)`,
      `tvm_mem (target:tvm_state)`, `8i:int`),
      cm_store_mem_word_other);
  fp_unchanged = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_store_width_def(), get_cm_type_int_char_distinct())),
      fp_unchanged);
  fp_unchanged = match_mp_rule(fp_unchanged, assume_rule(
      `cm_range_disjoint (base:int) 8i 8i 8i`));
  fp_unchanged = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_store_mem_def(), get_cm_type_int_char_distinct(),
      number_fixed)), fp_unchanged);
  thm new_fp = trans_rule(fp_unchanged, fp_word);
  thm frames_shape = mp_rule(
      ispec_rule(`frames:(cm_call_sim_frame)list`,
        get_theorem_by_name("CONS_HD_TL")), assume_rule(
        `~((frames:(cm_call_sim_frame)list) == [])`));
  thm calls_shape_view = beta_norm(ap_term_rule(
      `\fs:(cm_call_sim_frame)list.
         cm_call_frames_sim (tvm_mem (target:tvm_state)) fs
           (tvm_calls target)`,
      frames_shape));
  thm shaped_calls = eq_mp_rule(calls_shape_view, calls);
  thm opened_calls = conv_rule(
      rewrite_conv(THM_LIST(cm_call_frames_sim_def)),
      shaped_calls);
  thm calls_nonempty = conjunct1_rule(opened_calls);
  thm call_return = conjunct1_rule(conjunct2_rule(opened_calls));
  thm call_tail = conjunct2_rule(conjunct2_rule(
      conjunct2_rule(opened_calls)));
  thm new_tail = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `CMIntTy:cm_type`, `base:int`,
      `cm_state_fp (st:cm_src_state)`,
      `tvm_mem (target:tvm_state)`,
      `TL (frames:(cm_call_sim_frame)list)`,
      `TL (tvm_calls (target:tvm_state))`),
      cm_call_frames_store_sim), call_tail), assume_rule(
        `cm_call_frames_store_safe CMIntTy (base:int)
           (TL (frames:(cm_call_sim_frame)list))`));
  new_tail = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_store_mem_def(), get_cm_type_int_char_distinct(),
      number_fixed)), new_tail);
  thm new_head = specl_rule(TERM_LIST(
      `tvm_mem (target:tvm_state)`, `base:int`,
      `cm_state_fp (st:cm_src_state)`),
      get_tower_getw_setw());
  new_head = conv_rule(rewrite_conv(THM_LIST(
      number_fixed)), new_head);
  thm rebased_calls = conj_rule(calls_nonempty,
      conj_rule(call_return, conj_rule(new_head, new_tail)));
  term concrete_call_term =
      `cm_call_frames_sim
         (tower_setw (tvm_mem (target:tvm_state)) (base:int)
           (cm_state_fp (st:cm_src_state)))
         (CMCallSimFrame base
            (cm_call_sim_saved
              (HD (frames:(cm_call_sim_frame)list)))
            (cm_call_sim_return (HD frames)) ::
          TL frames)
         (tvm_calls target)`;
  thm concrete_call_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_call_frames_sim_def, cm_call_sim_base_def,
        cm_call_sim_saved_def, cm_call_sim_return_def,
        assume_rule(
          `cm_call_sim_saved
             (HD (frames:(cm_call_sim_frame)list)) ==
           cm_state_fp (st:cm_src_state)`))),
      concrete_call_term);
  thm concrete_calls = eq_mp_rule(
      sym_rule(concrete_call_view), rebased_calls);
  thm rebase_equal = beta_norm(ap_term_rule(
      `\fs:(cm_call_sim_frame)list.
         cm_rebase_call_frames (base:int) fs`,
      frames_shape));
  rebase_equal = conv_rule(
      rewrite_conv(THM_LIST(cm_rebase_call_frames_def)),
      rebase_equal);
  thm rebased_call_view = beta_norm(ap_term_rule(
      `\fs:(cm_call_sim_frame)list.
         cm_call_frames_sim
           (tower_setw (tvm_mem (target:tvm_state)) (base:int)
             (cm_state_fp (st:cm_src_state)))
           fs (tvm_calls target)`,
      rebase_equal));
  thm new_calls = eq_mp_rule(
      sym_rule(rebased_call_view), concrete_calls);
  thm new_spills = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`,
      `tvm_mem (target:tvm_state)`, `base:int`,
      `cm_state_fp (st:cm_src_state)`,
      `spill_frames:(cm_spill_frame)list`),
      get_cm_spill_frames_scratch_store_sim()), spills), assume_rule(
        `cm_spill_frames_store_safe (p:cm_program) CMIntTy
           (base:int) (spill_frames:(cm_spill_frame)list)`)),
      number_signed);
  thm old_stack = conv_rule(rewrite_conv(THM_LIST(
      cm_operand_suffix_sim_def)), operand);
  thm new_stack = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        old_stack, cm_encode_values_def,
        get_cm_value_number_def(), number_fixed,
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
      `TL (TL (tvm_stack (target:tvm_state))) ==
       cm_encode_values (st:cm_src_state) (values:(cm_value)list) ++
         (suffix:(int)list)`));
  thm new_operand = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_operand_suffix_sim_def)),
      `cm_operand_suffix_sim (st:cm_src_state)
         (values:(cm_value)list) (suffix:(int)list)
         (TL (TL (tvm_stack (target:tvm_state))))`)), new_stack);
  thm result = conj_rule(new_initialized,
      conj_rule(new_provenance,
      conj_rule(new_fp,
      conj_rule(new_calls,
      conj_rule(new_spills,
      conj_rule(input_equal,
      conj_rule(output_equal, new_operand)))))));
  thm_list rules = THM_LIST(
      cm_machine_sim_parts, get_tvm_next_state_def(),
      get_tvm_state_selectors_def());
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  ACCEPT_TAC(opened, conv_rule(reduce_rewrite_conv(rules), result));
  return gnode_prove(root);
}
PROOF thm cm_machine_call_save = cm_prove_machine_call_save();

PROOF static thm cm_prove_target_call_save(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (base:int) (values:(cm_value)list) (ann:cm_annotation)
         (target:tvm_task) (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst TVMStoreOp 0i :: rest) ==>
         cm_running_target_sim p fid st
           (CMIntV base :: CMIntV (cm_state_fp st) :: values)
           ann target ==>
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
         tower_signed64 base ==>
         tower_word_valid base ==>
         cm_running_target_sim p fid st values
           (cm_ann_call_rebase base
             (cm_ann_linear [TVMInst TVMStoreOp 0i] ann))
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
         (cm_ann_pc (ann:cm_annotation))
         (TVMInst TVMStoreOp 0i :: (rest:(tvm_inst)list))`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
         (st:cm_src_state)
         (CMIntV (base:int) :: CMIntV (cm_state_fp st) ::
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
         (cm_active_spill_frames (fid:int) st ann)
         (CMIntV (base:int) :: CMIntV (cm_state_fp st) ::
           (values:(cm_value)list)) []`);
  thm target_equal = conjunct1_rule(body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(body));
  thm machine = conjunct2_rule(conjunct2_rule(body));
  thm stack_length = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `CMIntV (base:int) :: CMIntV (cm_state_fp st) ::
        (values:(cm_value)list)`, `[]:(int)list`),
      get_cm_machine_sim_stack_length()), machine);
  thm stack_two = mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) ==
         (1i + 1i + ilength (values:(cm_value)list)) + 0i ==>
       0i <= ilength values ==>
       2i <= ilength (tvm_stack vm)`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  stack_two = match_mp_rule(stack_two,
      ispec_rule(`values:(cm_value)list`,
        get_theorem_by_name("ILENGTH_NONNEG")));
  thm stack_shape = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `CMIntV (base:int) :: CMIntV (cm_state_fp st) ::
        (values:(cm_value)list)`, `[]:(int)list`),
      get_cm_machine_sim_stack_shape()), machine);
  thm base_fixed = mp_rule(spec_rule(
      `base:int`, get_tower_wrap64_fixed()), assume_rule(
        `tower_signed64 (base:int)`));
  thm fp_fixed = mp_rule(spec_rule(
      `cm_state_fp (st:cm_src_state)`, get_tower_wrap64_fixed()),
      assume_rule(`tower_signed64 (cm_state_fp (st:cm_src_state))`));
  thm head_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        stack_shape, cm_encode_values_def, get_cm_value_number_def(),
        base_fixed, fp_fixed, get_theorem_by_name("APPEND"),
        get_theorem_by_name("HD"))),
      `HD (tvm_stack (vm:tvm_state)) == (base:int)`));
  thm second_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        stack_shape, cm_encode_values_def, get_cm_value_number_def(),
        base_fixed, fp_fixed, get_theorem_by_name("APPEND"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
      `HD (TL (tvm_stack (vm:tvm_state))) ==
       cm_state_fp (st:cm_src_state)`));
  thm address_valid = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(head_equal))), assume_rule(
        `tower_word_valid (base:int)`));
  term next =
      `tvm_next_state (vm:tvm_state)
         (TL (TL (tvm_stack vm))) (tvm_calls vm)
         (tower_setw (tvm_mem vm) (base:int)
           (cm_state_fp (st:cm_src_state)))
         (tvm_input vm) (tvm_output vm)`;
  thm action = specl_rule(TERM_LIST(
      `tvm_object_code (cm_compile_model (p:cm_program))`,
      `0i:int`, `vm:tvm_state`), get_tvm_store_transition());
  action = conv_rule(reduce_rewrite_conv(THM_LIST(
      stack_two, address_valid, head_equal, second_equal)), action);
  thm compiled_code = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
         (tvm_object_code (cm_compile_model (p:cm_program)))
         (tvm_pc (vm:tvm_state))
         (TVMInst TVMStoreOp 0i :: (rest:(tvm_inst)list))`));
  thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
      `TVMStoreOp:tvm_opcode`, `0i:int`,
      `rest:(tvm_inst)list`, next), cm_tvm_state_iter_one),
      compiled_code), action);
  stepped = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(target_equal))), stepped);
  thm machine_after = mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(
      mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
          `cm_ann_calls (ann:cm_annotation)`,
          `cm_active_spill_frames (fid:int) st ann`,
          `base:int`, `values:(cm_value)list`, `[]:(int)list`),
          cm_machine_call_save), machine), assume_rule(
            `~(cm_ann_calls (ann:cm_annotation) == [])`)),
          assume_rule(
            `cm_call_sim_base (HD (cm_ann_calls (ann:cm_annotation))) ==
             8i`)),
        assume_rule(
          `cm_call_sim_saved (HD (cm_ann_calls (ann:cm_annotation))) ==
           cm_state_fp (st:cm_src_state)`)),
      assume_rule(`cm_tagged_span_valid (st:cm_src_state)`)),
      assume_rule(
        `!addr.
           cm_live_address (st:cm_src_state) addr ==>
           ~((base:int) <= addr && addr < base + 8i)`)),
      assume_rule(`cm_range_disjoint (base:int) 8i 8i 8i`)),
      assume_rule(
        `cm_call_frames_store_safe CMIntTy (base:int)
           (TL (cm_ann_calls (ann:cm_annotation)))`)),
      assume_rule(
        `cm_spill_frames_store_safe (p:cm_program) CMIntTy
           (base:int)
           (cm_active_spill_frames (fid:int) st ann)`)),
      assume_rule(`tower_signed64 (cm_state_fp (st:cm_src_state))`));
  term updated =
      `cm_ann_call_rebase (base:int)
         (cm_ann_linear [TVMInst TVMStoreOp 0i]
           (ann:cm_annotation))`;
  thm next_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_tvm_next_state_def(), get_tvm_state_selectors_def(),
        cm_ann_call_rebase_def, cm_ann_linear_def,
        cm_ann_plain_def, cm_ann_pc_def,
        get_theorem_by_name("ILENGTH_DEF"), pc_equal)),
      `tvm_pc ${next:tvm_state} ==
       cm_ann_pc ${updated:cm_annotation}`));
  thm normalized_body =
      conj_rule(stepped, conj_rule(next_pc, machine_after));
  thm_list update_rules = THM_LIST(
      cm_ann_call_rebase_def, cm_rebase_call_frames_def,
      cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_pc_def, cm_ann_calls_def,
      cm_ann_spills_def, cm_ann_saved_def,
      cm_active_spill_frames_def,
      get_theorem_by_name("ILENGTH_DEF"));
  normalized_body = conv_rule(
      reduce_rewrite_conv(update_rules), normalized_body);
  term exists_goal =
      `?next_vm.
         tvm_iter 1 (target:tvm_task) ==
           TVMRunTask (cm_compile_model (p:cm_program)) next_vm &&
         tvm_pc next_vm == cm_ann_pc ${updated:cm_annotation} &&
         cm_machine_state_sim p (st:cm_src_state) next_vm
           (cm_ann_calls ${updated:cm_annotation})
           (cm_active_spill_frames (fid:int) st
             ${updated:cm_annotation})
           (values:(cm_value)list) []`;
  dest_exists_results exists_parts = dest_exists(exists_goal);
  term instantiated_body = subst_one(next, exists_parts.v,
      exists_parts.tm);
  thm body_reduction = apply_conversion(
      reduce_rewrite_conv(update_rules), instantiated_body);
  thm adjusted_body = eq_mp_rule(
      sym_rule(body_reduction), normalized_body);
  thm witness = exists_rule(exists_goal, next, adjusted_body);
  thm selected = choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_running_target_sim_def)));
  ACCEPT_TAC(opened, selected);
  return gnode_prove(root);
}
PROOF thm cm_target_call_save = cm_prove_target_call_save();

PROOF thm get_cm_rebase_call_frames_def(void) {
  return cm_rebase_call_frames_def;
}
PROOF thm get_cm_ann_call_rebase_def(void) {
  return cm_ann_call_rebase_def;
}
PROOF thm get_cm_machine_call_save(void) {
  return cm_machine_call_save;
}
PROOF thm get_cm_target_call_save(void) {
  return cm_target_call_save;
}

PROOF static int cmc_preservation_target_call_frame_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_call_frame_axioms_before,
      "cmc_preservation_target_call_frame introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_call_frame_checks =
    cmc_preservation_target_call_frame_final_checks();
