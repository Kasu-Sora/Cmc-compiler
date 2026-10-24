#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_machine_store.h"
#include "cmc_preservation_runtime.h"
#include "cmc_preservation_target_store.h"

#require "cmc_preservation_machine_store.c"
#require "cmc_preservation_runtime.c"
#require "cmc_preservation_target_machine.c"

PROOF static size_t _cmc_preservation_target_store_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_target_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ptr:cm_value) (v:cm_value) (values:(cm_value)list)
         (ann:cm_annotation) (target:tvm_task)
         (ty:cm_type) (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst
             (if ty == CMCharTy then TVMStoreBOp else TVMStoreOp)
             0i :: rest) ==>
         cm_running_target_sim p fid st (ptr :: v :: values) ann target ==>
         cm_runtime_memory_layout p st (cm_ann_calls ann)
           (cm_active_spill_frames fid st ann) ==>
         cm_store_ok ty ptr st ==>
         (ty == CMCharTy || ty == CMIntTy || cm_is_pointer ty) ==>
         cm_live_span st (cm_value_number st ptr)
           (cm_store_width ty) ==>
         cm_running_target_sim p fid (cm_state_store ty ptr v st)
           values (cm_ann_linear (cm_store_code ty) ann)
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst
          (if (ty:cm_type) == CMCharTy
           then TVMStoreBOp else TVMStoreOp)
          0i :: (rest:(tvm_inst)list))`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        ((ptr:cm_value) :: (v:cm_value) :: (values:(cm_value)list))
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
         ((ptr:cm_value) :: (v:cm_value) ::
           (values:(cm_value)list)) []`);
  thm target_equal = conjunct1_rule(body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(body));
  thm machine = conjunct2_rule(conjunct2_rule(body));
  thm stack_length = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `(ptr:cm_value) :: (v:cm_value) :: (values:(cm_value)list)`,
      `[]:(int)list`), get_cm_machine_sim_stack_length()), machine);
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
  thm stack_head = conjunct1_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `ptr:cm_value`,
      `(v:cm_value) :: (values:(cm_value)list)`, `[]:(int)list`),
      get_cm_machine_sim_stack_head()), machine));
  thm stack_shape = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `(ptr:cm_value) :: (v:cm_value) :: (values:(cm_value)list)`,
      `[]:(int)list`), get_cm_machine_sim_stack_shape()), machine);
  thm stack_second = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        stack_shape, cm_encode_values_def,
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
      `HD (TL (tvm_stack (vm:tvm_state))) ==
       cm_value_number (st:cm_src_state) (v:cm_value)`));
  thm width_positive =
      spec_rule(`ty:cm_type`, get_cm_store_width_positive());
  thm address_bounds = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `st:cm_src_state`,
        `cm_ann_calls (ann:cm_annotation)`,
        `cm_active_spill_frames (fid:int) st ann`,
        `cm_value_number st (ptr:cm_value)`,
        `cm_store_width (ty:cm_type)`),
        get_cm_runtime_live_span_bounds()),
      assume_rule(
        `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
          (cm_ann_calls (ann:cm_annotation))
          (cm_active_spill_frames (fid:int) st ann)`)),
      assume_rule(
        `cm_live_span (st:cm_src_state)
          (cm_value_number st (ptr:cm_value))
          (cm_store_width (ty:cm_type))`)),
      width_positive);
  thm machine_safe = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `ty:cm_type`, `ptr:cm_value`), get_cm_runtime_store_safe()),
      assume_rule(
        `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
          (cm_ann_calls (ann:cm_annotation))
          (cm_active_spill_frames (fid:int) st ann)`)),
      assume_rule(
        `cm_store_ok (ty:cm_type) (ptr:cm_value) (st:cm_src_state)`));

  gnode_list cases =
      BOOL_CASES_TAC(leaf, `(ty:cm_type) == CMCharTy`, "Hchar");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    bool is_char = i == 0;
    thm char_case = assume_rule(is_char
        ? `(ty:cm_type) == CMCharTy`
        : `~((ty:cm_type) == CMCharTy)`);
    thm branch_code_at = conv_rule(
        reduce_rewrite_conv(THM_LIST(char_case)), code_at);
    term opcode = is_char
        ? `TVMStoreBOp:tvm_opcode`
        : `TVMStoreOp:tvm_opcode`;
    term new_mem = is_char
        ? `tower_setb (tvm_mem (vm:tvm_state))
            (cm_value_number (st:cm_src_state) (ptr:cm_value))
            (cm_value_number st (v:cm_value))`
        : `tower_setw (tvm_mem (vm:tvm_state))
            (cm_value_number (st:cm_src_state) (ptr:cm_value))
            (cm_value_number st (v:cm_value))`;
    term next =
        `tvm_next_state (vm:tvm_state)
          (TL (TL (tvm_stack vm))) (tvm_calls vm) ${new_mem:int->int}
          (tvm_input vm) (tvm_output vm)`;
    term address_valid = is_char
        ? `tower_addr_valid
            (cm_value_number (st:cm_src_state) (ptr:cm_value))`
        : `tower_word_valid
            (cm_value_number (st:cm_src_state) (ptr:cm_value))`;
    thm raw_bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
        char_case, get_cm_store_width_def())), address_bounds);
    term number =
        `cm_value_number (st:cm_src_state) (ptr:cm_value)`;
    thm raw_valid = match_mp_rule(
        is_char
          ? int_arith_rule(
              `0i <= ${number:int} &&
               ${number:int} + 1i <= 1048576i ==>
               0i <= ${number:int} &&
               ${number:int} < 1048576i`)
          : int_arith_rule(
              `0i <= ${number:int} &&
               ${number:int} + 8i <= 1048576i ==>
               0i <= ${number:int} &&
               ${number:int} + 7i < 1048576i`),
        raw_bounds);
    thm valid_expansion = apply_conversion(
        rewrite_conv(THM_LIST(
          is_char
            ? get_tower_addr_valid_def()
            : get_tower_word_valid_def())),
        address_valid);
    thm address_ok =
        eq_mp_rule(sym_rule(valid_expansion), raw_valid);
    thm action = specl_rule(TERM_LIST(
        `tvm_object_code (cm_compile_model (p:cm_program))`,
        `0i:int`, `vm:tvm_state`),
        is_char
          ? get_tvm_storeb_transition()
          : get_tvm_store_transition());
    action = conv_rule(reduce_rewrite_conv(THM_LIST(
        stack_two, stack_head, stack_second, address_ok)), action);
    thm compiled_code = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_compile_model_def(), get_tvm_object_code_def(),
          pc_equal, branch_code_at)),
        `cm_code_at
          (tvm_object_code (cm_compile_model (p:cm_program)))
          (tvm_pc (vm:tvm_state))
          (TVMInst ${opcode:tvm_opcode} 0i ::
            (rest:(tvm_inst)list))`));
    thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
        opcode, `0i:int`, `rest:(tvm_inst)list`, next),
        cm_tvm_state_iter_one), compiled_code), action);
    stepped = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(target_equal))), stepped);

    thm machine_after = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
        `cm_ann_calls (ann:cm_annotation)`,
        `cm_active_spill_frames (fid:int) st ann`,
        `ptr:cm_value`, `v:cm_value`, `values:(cm_value)list`,
        `[]:(int)list`, `ty:cm_type`), get_cm_machine_store()),
        machine), machine_safe);
    term updated =
        `cm_ann_linear (cm_store_code (ty:cm_type))
          (ann:cm_annotation)`;
    thm next_pc = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_tvm_next_state_def(), get_tvm_state_selectors_def(),
          cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
          get_cm_store_code_def(), get_theorem_by_name("ILENGTH_DEF"),
          char_case, pc_equal)),
        `tvm_pc ${next:tvm_state} ==
         cm_ann_pc ${updated:cm_annotation}`));
    thm normalized_body =
        conj_rule(stepped, conj_rule(next_pc, machine_after));
    thm_list update_rules = get_cm_state_core_defs();
    vector_add(&update_rules, get_cm_state_store_def());
    vector_add(&update_rules, cm_ann_linear_def);
    vector_add(&update_rules, cm_ann_plain_def);
    vector_add(&update_rules, cm_ann_pc_def);
    vector_add(&update_rules, cm_ann_calls_def);
    vector_add(&update_rules, cm_ann_spills_def);
    vector_add(&update_rules, cm_ann_saved_def);
    vector_add(&update_rules, cm_active_spill_frames_def);
    vector_add(&update_rules, get_cm_store_code_def());
    vector_add(&update_rules, get_theorem_by_name("ILENGTH_DEF"));
    vector_add(&update_rules, char_case);
    vector_add(&update_rules, stack_head);
    normalized_body =
        conv_rule(reduce_rewrite_conv(update_rules), normalized_body);
    term new_state =
        `cm_state_store (ty:cm_type) (ptr:cm_value)
          (v:cm_value) (st:cm_src_state)`;
    term exists_goal =
        `?next_vm.
           tvm_iter 1 (target:tvm_task) ==
             TVMRunTask (cm_compile_model (p:cm_program)) next_vm &&
           tvm_pc next_vm == cm_ann_pc ${updated:cm_annotation} &&
           cm_machine_state_sim p ${new_state:cm_src_state} next_vm
             (cm_ann_calls ${updated:cm_annotation})
             (cm_active_spill_frames (fid:int) ${new_state:cm_src_state}
               ${updated:cm_annotation})
             (values:(cm_value)list) []`;
    dest_exists_results exists_parts = dest_exists(exists_goal);
    term instantiated_body =
        subst_one(next, exists_parts.v, exists_parts.tm);
    thm body_reduction = apply_conversion(
        reduce_rewrite_conv(update_rules), instantiated_body);
    thm adjusted_body = eq_mp_rule(
        sym_rule(body_reduction), normalized_body);
    thm witness =
        exists_rule(exists_goal, next, adjusted_body);
    thm selected =
        choose_rule(`vm:tvm_state`, expanded, witness);
    gnode opened = CONV_TAC(cases[i],
        rewrite_conv(THM_LIST(cm_running_target_sim_def)));
    ACCEPT_TAC(opened, selected);
  }
  return gnode_prove(root);
}
PROOF thm cm_target_store = cm_prove_target_store();

PROOF thm get_cm_target_store(void) { return cm_target_store; }

PROOF static int cmc_preservation_target_store_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_store_axioms_before,
      "cmc_preservation_target_store introduced an axiom");
  ENSURE_COND(!IS_NULL(cm_target_store),
      "cm_target_store was not proved");
  ENSURE_COND(vector_size(hyp(cm_target_store)) == 0,
      "cm_target_store has hypotheses");
  return 0;
err:
  return -1;
}

PROOF static int _cmc_preservation_target_store_checks =
    cmc_preservation_target_store_final_checks();
