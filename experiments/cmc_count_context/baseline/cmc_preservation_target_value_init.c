#include "proof/proof.h"
#include "cmc_preservation_target_convert.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_value_init.h"
#include "cmc_preservation_code_value.h"
#include "cmc_preservation_target_address.h"
#include "cmc_preservation_target_store.h"
#include "cmc_preservation_store_semantic.h"

#require "cmc_preservation_target_value_return.c"
#require "cmc_preservation_target_address.c"
#require "cmc_preservation_target_store.c"
#require "cmc_preservation_store_semantic.c"

PROOF static size_t _cmc_preservation_target_value_init_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_target_init_code_suffix(
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

PROOF static thm cm_prove_target_v_init_step(void) {
  term ty = `ty:cm_type`;
  term ptr = `ptr:cm_value`;
  term offset = `cm_local_offset (p:cm_program) (fid:int) (slot:int)`;
  term converted =
      `cm_convert_value (st:cm_src_state) ${ty:cm_type} (v:cm_value)`;
  term new_state =
      `cm_state_store ${ty:cm_type} ${ptr:cm_value} (v:cm_value)
        (st:cm_src_state)`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (CMInitK (slot:int) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor (CAInitP (slot:int)) (owner:int)
          (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term body = imp_chain(TERM_LIST(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`,
      `cm_binding_address_ok (p:cm_program) (fid:int) 1i
        (slot:int) (st:cm_src_state)`,
      `${ty:cm_type} ==
        cm_slot_ty
          (inth (slot:int)
            (cm_function_locals
              (inth (fid:int)
                (cm_program_functions (p:cm_program)))))`,
      `${ptr:cm_value} ==
        cm_state_env (st:cm_src_state) 1i (slot:int)`,
      `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
        (calls:(cm_call_sim_frame)list)
        (CMSpillFrame (fid:int) (cm_state_fp st)
          (spills:(cm_spill)list) ::
         (saved:(cm_spill_frame)list))`,
      `cm_store_ok ${ty:cm_type} ${ptr:cm_value} (st:cm_src_state)`,
      `${ty:cm_type} == CMCharTy || ty == CMIntTy || cm_is_pointer ty`,
      `cm_live_span (st:cm_src_state)
        (cm_value_number st ${ptr:cm_value})
        (cm_store_width ${ty:cm_type})`,
      `tower_signed64 (cm_value_number (st:cm_src_state) (v:cm_value))`,
      `tower_signed64 (cm_state_fp (st:cm_src_state))`,
      `tower_signed64 ${offset:int}`,
      `(address:int) == cm_state_fp st + ${offset:int}`,
      `tower_signed64 (address:int)`,
      `tower_wrap64 (address:int) ==
        cm_value_number (st:cm_src_state) ${ptr:cm_value}`),
      `cm_task_target_sim (p:cm_program)
        (cm_step ${task:cm_task})
        (tvm_iter
          (cm_update_steps
            (cm_annotation_step ${task:cm_task} ${ann:cm_annotation}))
          (target:tvm_task))
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task} ${ann:cm_annotation}))`);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);

  term code = `cm_model_code (p:cm_program)`;
  term normalize_code = `cm_char_normalize_code ${ty:cm_type}`;
  term address_code = `cm_fp_relative_address_code ${offset:int}`;
  term store_code = `cm_store_code ${ty:cm_type}`;
  term code_rest =
      `cm_normal_cont_code (p:cm_program) (fid:int)
        ((pc:int) +
         ilength (cm_init_tail_code p fid (slot:int)))
        (owner:int) (rest:(cm_acursor)list)`;
  term suffix1 =
      `${address_code:(tvm_inst)list} ++
       ${store_code:(tvm_inst)list} ++
       ${code_rest:(tvm_inst)list}`;
  term suffix2 =
      `${store_code:(tvm_inst)list} ++
       ${code_rest:(tvm_inst)list}`;
  term ann1 =
      `cm_ann_linear ${normalize_code:(tvm_inst)list}
        ${ann:cm_annotation}`;
  term ann2 =
      `cm_ann_linear ${address_code:(tvm_inst)list}
        ${ann1:cm_annotation}`;
  term ann3 =
      `cm_ann_linear ${store_code:(tvm_inst)list}
        ${ann2:cm_annotation}`;
  term target1 =
      `tvm_iter (cm_code_steps ${normalize_code:(tvm_inst)list})
        (target:tvm_task)`;
  term target2 = `tvm_iter 4 ${target1:tvm_task}`;
  term target3 = `tvm_iter 1 ${target2:tvm_task}`;

  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm opened = conv_rule(
      reduce_rewrite_conv(cm_v_layout_rules()), layout);
  thm old_code = conjunct1_rule(opened);
  thm_list code_rules = cm_v_layout_rules();
  vector_add(&code_rules, assume_rule(
      `${ty:cm_type} ==
        cm_slot_ty
          (inth (slot:int)
            (cm_function_locals
              (inth (fid:int)
                (cm_program_functions (p:cm_program)))))`));
  vector_add(&code_rules, cm_init_tail_code_def);
  vector_add(&code_rules, get_cm_char_normalize_code_def());
  vector_add(&code_rules, get_cm_fp_relative_address_code_def());
  vector_add(&code_rules, get_cm_store_code_def());
  vector_add(&code_rules, get_cm_push_code_def());
  vector_add(&code_rules, cm_ann_linear_def);
  vector_add(&code_rules, cm_ann_plain_def);
  vector_add(&code_rules, cm_active_spill_frames_def);
  vector_add(&code_rules, get_theorem_by_name("APPEND"));
  vector_add(&code_rules, get_theorem_by_name("APPEND_NIL"));
  vector_add(&code_rules, get_theorem_by_name("ILENGTH_DEF"));
  old_code = conv_rule(reduce_rewrite_conv(code_rules), old_code);
  thm code1 = cm_target_init_code_suffix(
      old_code, code, ann, normalize_code, suffix1, ann1,
      code_rules);
  thm code2 = cm_target_init_code_suffix(
      code1, code, ann1, address_code, suffix2, ann2,
      code_rules);

  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(
        `cm_task_target_sim (p:cm_program) ${task:cm_task}
          (target:tvm_task) ${ann:cm_annotation}`));
  thm binding_ok = assume_rule(
      `cm_binding_address_ok (p:cm_program) (fid:int) 1i
        (slot:int) (st:cm_src_state)`);
  thm normalized = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, ty,
      `v:cm_value`, `[]:(cm_value)list`, ann,
      `target:tvm_task`, suffix1), get_cm_target_char_normalize());
  normalized = conv_rule(reduce_rewrite_conv(code_rules), normalized);
  normalized = match_mp_rule(normalized, old_code);
  normalized = match_mp_rule(normalized, running);
  normalized = match_mp_rule(normalized, assume_rule(
      `tower_signed64
        (cm_value_number (st:cm_src_state) (v:cm_value))`));

  thm addressed = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, offset,
      `address:int`, ptr, `[${converted:cm_value}]:(cm_value)list`,
      ann1, target1, suffix2), get_cm_target_fp_relative_address());
  addressed = conv_rule(reduce_rewrite_conv(code_rules), addressed);
  addressed = match_mp_rule(addressed,
      conv_rule(reduce_rewrite_conv(code_rules), code1));
  addressed = match_mp_rule(addressed, normalized);
  addressed = match_mp_rule(addressed, assume_rule(
      `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  addressed = match_mp_rule(addressed,
      assume_rule(`tower_signed64 ${offset:int}`));
  addressed = match_mp_rule(addressed, assume_rule(
      `(address:int) == cm_state_fp (st:cm_src_state) + ${offset:int}`));
  addressed = match_mp_rule(addressed,
      assume_rule(`tower_signed64 (address:int)`));
  addressed = match_mp_rule(addressed, assume_rule(
      `tower_wrap64 (address:int) ==
        cm_value_number (st:cm_src_state) ${ptr:cm_value}`));

  thm runtime = assume_rule(
      `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
        (calls:(cm_call_sim_frame)list)
        (CMSpillFrame (fid:int) (cm_state_fp st)
          (spills:(cm_spill)list) ::
         (saved:(cm_spill_frame)list))`);
  thm store_ok = assume_rule(
      `cm_store_ok ${ty:cm_type} ${ptr:cm_value} (st:cm_src_state)`);
  thm kinds = assume_rule(
      `${ty:cm_type} == CMCharTy || ty == CMIntTy || cm_is_pointer ty`);
  thm live = assume_rule(
      `cm_live_span (st:cm_src_state)
        (cm_value_number st ${ptr:cm_value})
        (cm_store_width ${ty:cm_type})`);
  thm stored = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, ptr, converted,
      `[]:(cm_value)list`, ann2, target2, ty, code_rest),
      get_cm_target_store());
  stored = conv_rule(reduce_rewrite_conv(code_rules), stored);
  stored = match_mp_rule(stored,
      conv_rule(reduce_rewrite_conv(code_rules), code2));
  stored = match_mp_rule(stored, addressed);
  stored = match_mp_rule(stored,
      conv_rule(reduce_rewrite_conv(code_rules), runtime));
  stored = match_mp_rule(stored,
      conv_rule(reduce_rewrite_conv(code_rules), store_ok));
  stored = match_mp_rule(stored,
      conv_rule(reduce_rewrite_conv(code_rules), kinds));
  stored = match_mp_rule(stored,
      conv_rule(reduce_rewrite_conv(code_rules), live));
  thm store_equality = specl_rule(TERM_LIST(
      ty, ptr, `v:cm_value`, `st:cm_src_state`),
      get_cm_state_store_converted());
  stored = conv_rule(rewrite_conv(THM_LIST(store_equality)), stored);

  term final_ann =
      `cm_ann_pop
        ((pc:int) + ilength
          (cm_init_tail_code (p:cm_program) (fid:int) (slot:int)))
        ${ann:cm_annotation}`;
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, new_state,
      `[]:(cm_value)list`, ann3, final_ann, target3),
      get_cm_target_reannotate());
  thm_list ann_rules = (thm_list)vector_copy(code_rules);
  vector_add(&ann_rules, cm_ann_pop_def);
  for (size_t premise = 0; premise < 4; ++premise) {
    term wanted = dest_imp(concl(reannotated)).tm1;
    thm wanted_view = apply_conversion(
        reduce_rewrite_conv(ann_rules), wanted);
    thm wanted_normal = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(ann_rules), rhs_of(wanted_view)));
    reannotated = match_mp_rule(reannotated,
        eq_mp_rule(sym_rule(wanted_view), wanted_normal));
  }
  reannotated = conv_rule(reduce_rewrite_conv(code_rules), reannotated);
  thm result = match_mp_rule(reannotated, stored);


  thm type_equal = assume_rule(
      `${ty:cm_type} ==
        cm_slot_ty
          (inth (slot:int)
            (cm_function_locals
              (inth (fid:int)
                (cm_program_functions (p:cm_program)))))`);
  thm pointer_equal = assume_rule(
      `${ptr:cm_value} == cm_state_env (st:cm_src_state) 1i (slot:int)`);
  thm source_store_ok = conv_rule(
      rewrite_conv(THM_LIST(type_equal, pointer_equal)), store_ok);
  thm_list finish_rules = cm_v_layout_rules();
  vector_add(&finish_rules, type_equal);
  vector_add(&finish_rules, pointer_equal);
  vector_add(&finish_rules, source_store_ok);
  vector_add(&finish_rules, cm_init_tail_code_def);
  vector_add(&finish_rules, get_cm_char_normalize_code_def());
  vector_add(&finish_rules, get_cm_fp_relative_address_code_def());
  vector_add(&finish_rules, get_cm_store_code_def());
  vector_add(&finish_rules, get_cm_push_code_def());
  vector_add(&finish_rules, cm_task_target_sim_def);
  vector_add(&finish_rules, binding_ok);
  vector_add(&finish_rules, cm_running_target_sim_def);
  vector_add(&finish_rules, cm_active_spill_frames_def);
  vector_add(&finish_rules, cm_update_steps_def);
  vector_add(&finish_rules, cm_code_steps_def);
  vector_add(&finish_rules, cm_ann_linear_def);
  vector_add(&finish_rules, cm_ann_plain_def);
  vector_add(&finish_rules, cm_ann_pop_def);
  vector_add(&finish_rules, get_cm_state_store_converted());
  vector_add(&finish_rules, get_theorem_by_name("APPEND"));
  vector_add(&finish_rules, get_theorem_by_name("APPEND_NIL"));
  vector_add(&finish_rules, get_theorem_by_name("ILENGTH_APPEND"));
  vector_add(&finish_rules, get_theorem_by_name("ILENGTH_DEF"));
  thm_list numerals = THM_LIST();
  term_list numeral_terms = TERM_LIST(
      `0:num`, `1:num`, `4:num`, `5:num`, `6:num`, `11:num`);
  for (size_t index = 0; index < vector_size(numeral_terms); ++index) {
    vector_add(&numerals, spec_rule(
        numeral_terms[index], get_theorem_by_name("NUM_OF_INT_OF_NUM")));
  }
  gnode_list char_cases = BOOL_CASES_TAC(
      leaf, `${ty:cm_type} == CMCharTy`, "Hchar");
  for (size_t index = 0; index < 2; ++index) {
    thm char_case = assume_rule(index == 0
        ? `${ty:cm_type} == CMCharTy`
        : `~(${ty:cm_type} == CMCharTy)`);
    thm source_char_case = conv_rule(
        rewrite_conv(THM_LIST(type_equal)), char_case);
    thm_list branch_rules = (thm_list)vector_copy(finish_rules);
    vector_add(&branch_rules, char_case);
    vector_add(&branch_rules, source_char_case);
    term initial_steps = index == 0 ? `6:num` : `0:num`;
    term accumulated_steps =
        index == 0 ? `(6:num) + 4` : `(0:num) + 4`;
    thm iter_address = specl_rule(TERM_LIST(
        initial_steps, `4:num`, `target:tvm_task`),
        get_cm_tvm_iter_add());
    thm iter_store = specl_rule(TERM_LIST(
        accumulated_steps, `1:num`, `target:tvm_task`),
        get_cm_tvm_iter_add());
    term total_steps =
        index == 0 ? `((6:num) + 4) + 1` : `((0:num) + 4) + 1`;
    vector_add(&branch_rules, apply_conversion(
        get_conversion_by_name("NUM_REDUCE_CONV"), total_steps));
    conv normalize = then_conv(
        then_conv(
          then_conv(reduce_rewrite_conv(branch_rules),
            rewrite_conv(numerals)),
          reduce_rewrite_conv(branch_rules)),
        reduce_rewrite_conv(branch_rules));
    thm branch_result = conv_rule(
        reduce_rewrite_conv(THM_LIST(source_char_case)), result);
    branch_result = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_code_steps_def, get_cm_char_normalize_code_def(),
        source_char_case, get_theorem_by_name("ILENGTH_DEF"))),
        branch_result);
    branch_result = conv_rule(rewrite_conv(numerals), branch_result);
    branch_result = conv_rule(
        rewrite_conv(THM_LIST(sym_rule(iter_address))), branch_result);
    branch_result = conv_rule(
        rewrite_conv(THM_LIST(sym_rule(iter_store))), branch_result);
    thm normalized_result = conv_rule(normalize, branch_result);
    thm target_view = apply_conversion(
        normalize, goal_ccl(char_cases[index]->g));
    ACCEPT_TAC(char_cases[index],
        eq_mp_rule(sym_rule(target_view), normalized_result));
  }
  return gnode_prove(root);
}

PROOF thm cm_target_v_init_step = cm_prove_target_v_init_step();

PROOF thm get_cm_target_v_init_step(void) {
  return cm_target_v_init_step;
}

PROOF static int cmc_preservation_target_value_init_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_init_axioms_before,
      "cmc_preservation_target_value_init introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_value_init_checks =
    cmc_preservation_target_value_init_final_checks();
